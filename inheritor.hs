{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{- Inheritance from parent to their children or their cousins 
    There's 3 Endpoint : 
    1. Inherit : To submit the inherition to someone selected with pin 
    2. Retrieve: To get The Inherition with submit the Pin, Retrieval need deadline to be reached first
    3. Close : To cancel The Inherition , Close executed by the Owner and no need to reached deadline

    First Point : 
    - Inherit can be done several times from Person A to Person B 
    The Result will be like this 
    Transaction 1 : 
        Person A Inherit with Pin 1234 deadline 10 slot to Person B
    Transaction 2: 
        Person A Inherit with Pin 3584 deadline 5 slot to Person B 
    As long as the The Inheritor and the Beneficiary is same. 
    It will be summarize into one UTXO , When UTXO is summarized into new UTXO, the deadline will be counted since the new UTXO
    For Transaction 1: 
        Person A pay to Script (UTXO 1)
    For Transaction 2: 
        Spending Transaction from UTXO 1 to Person A (The OWner) and then pay to the Script with total amount of Transaction 1 + Transaction 2 
        and because of the beneficiary and the owner is same from transaction 1 and 2 , The pin, deadline will be replaced for the last Transaction 

        So The Current Exist UTXO Only 1
        pin 3584
        deadline 5 slot
        Beneficiary Person B
        Amount : Total of T1 + T2
    
    Second Point : 
    - Retrieval only can be happened if the beneficiary have the right pin. And the beneficiary is already selected by the previous Inheritor 
    If there's no Inheritor inherit to the Retrieval, even if they have the pin. The amount can't be retrieved

    Retrieval with the right Pin and have Inheritors that selected him/her as beneficiary can get All the Inheritors with the giving pin from Retrieval
    Retrieval can be retrieved when already reached the minimum deadline 
    And the deadline is counted since the Last Updated UTXO 

    Case : 
    Trasanction 1
        Person a -> Person b With Pin 1234568
    Transaction 2
        Person a -> Person b With Pin 123456
    Transaction 3
        Person c -> Person b With Pin 123456
    Note -> is Inherit 

    With the case above : 
    Transaction 1 will be replaced to transaction 2 
        Transaction 2 will have amount of Total Transaction 1 + 2 with the Pin 123456
    Transaction 3 will have Pin 123456
    And then for Transaction 4
    Person b Retrieve with Pin 123456
    So Person b can get The Transaction 2 + Transaction 3 

    if Person d Retrieve with the right Pin : Person d won't get anything because no one inherit to Person D 

    Third Point :
    - Close / Cancel can only be done by the inheritor / Owner of the Inheritor and must have the right pin 

    Case Transaction 1 
        Person a -> Person b with Pin 123456
    Case Transaction 2 
        Person a -> Person b with Pin 35678
    Case Transaction 3 
        Person a -> Person b with Pin 35678
    Note -> is Inherit 
    The Transaction 1 will be replaced with Transaction 2
        Transaction 2 will have amount Total of Transaction 1 + 2 with Pin 35678
    Person a want to close with Pin 35678
    Person a will have Transaction 2 and Transaction 3   


    If the UTXO is summarized because of the Inheritor and beneficirary is same.
    The deadline will be counted from the Last UTXO Beneficiary and Inheritor is same.
    
 -}

import           Control.Monad        hiding (fmap)
import           Data.Aeson           (ToJSON, FromJSON)
import           Data.Map             as Map
import           Data.Text            (Text)
import           Data.Void            (Void)
import           GHC.Generics         (Generic)
import           Plutus.Contract
import           PlutusTx             (Data (..))
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import           Ledger               hiding (singleton)
import           Ledger.Constraints   (TxConstraints)
import qualified Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Ada           as Ada
import           Playground.Contract  (printJson, printSchemas, ensureKnownCurrencies, stage, ToSchema)
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (IO, Semigroup (..), Show (..), String)
import           Text.Printf          (printf)

data Retr = Retr
    { retrPin :: !Integer
    , retraddr    :: !PaymentPubKeyHash
    } deriving Show

instance Eq Retr where 
    {-# INLINABLE (==) #-}
    b == c = ( retrPin b == retrPin c) &&
             ( retraddr b == retraddr c)

PlutusTx.unstableMakeIsData ''Retr
PlutusTx.makeLift ''Retr


data RetrAuction = MkRet Retr | Close Retr
    deriving Show

PlutusTx.unstableMakeIsData ''RetrAuction
PlutusTx.makeLift ''RetrAuction

data InheritDatum = InheritDatum
    { beneficiary :: PaymentPubKeyHash
    , owner       :: PaymentPubKeyHash
    , deadline    :: POSIXTime
    , pin         :: Integer
    , amount      :: Integer
    } deriving Show

PlutusTx.makeLift ''InheritDatum
PlutusTx.unstableMakeIsData ''InheritDatum


{-# INLINABLE mkValidator #-}
mkValidator :: InheritDatum -> RetrAuction -> ScriptContext -> Bool
mkValidator dat redeemer ctx = 
    traceIfFalse "Wrong Input Datum" checkInput && 
    case redeemer of 
        MkRet ret -> 
            traceIfFalse "Pin Must be right" (checkOnlyBeneficiaryWithPin ret) &&
            traceIfFalse "deadline not reached" (deadlineForBeneficiary ret) 
        Close ret -> traceIfFalse "Only Owner with Right Pin can cancel Transaction" (checkOwnerWithRightPin ret)
    where 
        info :: TxInfo
        info = scriptContextTxInfo ctx

        checkInput :: Bool
        checkInput = beneficiary dat /= owner dat

        isBeneficiary :: Retr -> Bool
        isBeneficiary ret= beneficiary dat == retraddr ret

        isOwner :: Retr -> Bool
        isOwner ret= owner dat == retraddr ret

        checkDeadlineTo :: Bool
        checkDeadlineTo = from (deadline dat) `contains` txInfoValidRange info

        checkPin :: Retr -> Bool
        checkPin ret= pin dat == retrPin ret

        checkOnlyBeneficiaryWithPin :: Retr -> Bool
        checkOnlyBeneficiaryWithPin ret = (isBeneficiary ret && checkPin ret) || (isOwner ret)

        checkOwnerWithRightPin :: Retr -> Bool
        checkOwnerWithRightPin ret = (isOwner ret && checkPin ret)

        deadlineForBeneficiary :: Retr -> Bool
        deadlineForBeneficiary ret = (checkDeadlineTo && isBeneficiary ret) || (isOwner ret)
data Vesting
instance Scripts.ValidatorTypes Vesting where
    type instance RedeemerType Vesting = RetrAuction
    type instance DatumType Vesting = InheritDatum    

typedValidator :: Scripts.TypedValidator Vesting
typedValidator = Scripts.mkTypedValidator @Vesting
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @InheritDatum @RetrAuction

validator :: Validator
validator = Scripts.validatorScript typedValidator

valHash :: Ledger.ValidatorHash
valHash = Scripts.validatorHash typedValidator

scrAddress :: Ledger.Address
scrAddress = scriptAddress validator

data InheritParam = InheritParam {
    gpBeneficiary :: PaymentPubKeyHash,
    gpDeadline    :: POSIXTime,
    gpPin         :: Integer,
    gpAmount      :: Integer
} deriving (Generic, ToJSON, FromJSON, ToSchema)

data RetParam = RetParam {
    retPin      ::  Integer
} deriving (Generic, ToJSON, FromJSON, ToSchema)


type InheritSchema =
            Endpoint "close" RetParam
        .\/ Endpoint "Inherit" InheritParam
        .\/ Endpoint "Retrieve" RetParam


inherit :: forall w s. InheritParam -> Contract w s Text ()
inherit InheritParam{..} = do
    now <- currentTime
    pkh <- ownPaymentPubKeyHash
    utxosFlag <- findInitiateFlag gpBeneficiary pkh
    logInfo @String $ printf "masuk inherit kok"
    if utxosFlag == True 
        then do
            logInfo @String $ printf "True Kok"
            (oref, o, d@InheritDatum{..}) <- findInitiate gpBeneficiary pkh
            let payment = amount + gpAmount
                dat     = InheritDatum{
                    beneficiary = gpBeneficiary,
                    owner       = pkh,
                    deadline    = gpDeadline,
                    pin         = gpPin,
                    amount      = payment
                }
                ret = Retr {
                    retrPin = gpPin,
                    retraddr = pkh
                }
                r  = Redeemer $ PlutusTx.toBuiltinData $ MkRet ret
                v = Ada.lovelaceValueOf payment
                lookups =   Constraints.typedValidatorLookups typedValidator <>
                            Constraints.otherScript validator <>
                            Constraints.unspentOutputs (Map.singleton oref o)  
                            
                tx      = Constraints.mustPayToTheScript dat v  <> 
                        Constraints.mustSpendScriptOutput oref r 
                         
            ledgerTx <- submitTxConstraintsWith lookups tx
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            logInfo @String $ "Contract Updated"
        else do
            let dat     = InheritDatum{
                    beneficiary = gpBeneficiary,
                    owner       = pkh,
                    deadline    = gpDeadline,
                    pin         = gpPin,
                    amount      = gpAmount
                }
                tx      = Constraints.mustPayToTheScript dat $ Ada.lovelaceValueOf gpAmount
            
            ledgerTx <- submitTxConstraints typedValidator tx
            logInfo @String $ printf "False Kok %s %s" (show gpAmount) (show dat)
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            logInfo @String $ "Contract Initiated Created"

retrieve :: forall w s. RetParam -> Contract w s Text ()
retrieve RetParam{..} = do
    now   <- currentTime
    pkh   <- ownPaymentPubKeyHash
    utxos <- Map.filter (isSuitable pkh) <$> utxosAt scrAddress
    if Map.null utxos
        then logInfo @String $ printf "Retrieve Failed because of Pin or Beneficiary %s Not Exist" (show pkh)
        else do
            logInfo @String $ printf "masuk %s %s" (show pkh) (show retPin)
            let orefs = fst <$> Map.toList utxos
                lookups = Constraints.unspentOutputs utxos  <>
                          Constraints.otherScript validator
                ret = Retr {
                    retrPin = retPin,
                    retraddr = pkh
                }
                r  = Redeemer $ PlutusTx.toBuiltinData $ MkRet ret
                tx :: TxConstraints Void Void
                tx      = mconcat[Constraints.mustSpendScriptOutput oref r  | oref <- orefs] <>
                         Constraints.mustValidateIn (from now)
            ledgerTx <- submitTxConstraintsWith @Void lookups tx
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            logInfo @String $ printf "Retrieval Succedd"
    where
        isSuitable :: PaymentPubKeyHash -> ChainIndexTxOut -> Bool
        isSuitable pkh o = case _ciTxOutDatum o of
            Left _          -> False
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> False
                Just d  -> beneficiary d == pkh && pin d == retPin 

close :: forall w s. RetParam -> Contract w s Text ()
close RetParam{..} = do
    now   <- currentTime
    pkh <- ownPaymentPubKeyHash
    utxos <- Map.filter (isSuitable pkh) <$> utxosAt scrAddress
    if Map.null utxos
        then logInfo @String $ printf "Close Failed because of Pin or Beneficiary %s Not Exist" (show pkh)
        else do
            let orefs   = fst <$> Map.toList utxos
                lookups = Constraints.unspentOutputs utxos  <>
                          Constraints.otherScript validator
                ret = Retr {
                    retrPin = retPin,
                    retraddr = pkh
                }
                r  = Redeemer $ PlutusTx.toBuiltinData $ MkRet ret
                tx :: TxConstraints Void Void
                tx      = mconcat [Constraints.mustSpendScriptOutput oref r | oref <- orefs]
            ledgerTx <- submitTxConstraintsWith @Void lookups tx
            void $ awaitTxConfirmed $ getCardanoTxId ledgerTx
            logInfo @String $ "Close Succedd"
    where
        isSuitable :: PaymentPubKeyHash -> ChainIndexTxOut -> Bool
        isSuitable pkh o = case _ciTxOutDatum o of
            Left _          -> False
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> False
                Just d  -> pin d == retPin && owner d == pkh

findInitiate :: PaymentPubKeyHash -> PaymentPubKeyHash  -> Contract w s Text (TxOutRef, ChainIndexTxOut, InheritDatum)
findInitiate _bene _own = do
    utxos <- utxosAt scrAddress
    let xs = [ (oref, o)
             | (oref, o) <- Map.toList utxos ]
    case xs of
        [(oref, o)] -> case _ciTxOutDatum o of
            Left _          -> throwError "Datum Missing"
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> throwError "Datum has wrong type"
                Just d@InheritDatum{..}
                    | beneficiary == _bene && _own == owner -> return (oref, o, d)
                    | otherwise                                           -> throwError "auction token missmatch"
        _           -> throwError "No Contract "

findInitiateFlag :: PaymentPubKeyHash -> PaymentPubKeyHash -> Contract w s Text (Bool)
findInitiateFlag _bene _own = do
    utxos <- utxosAt scrAddress
    let xs = [ (oref, o)
             | (oref, o) <- Map.toList utxos ]
    case xs of
        [(oref, o)] -> case _ciTxOutDatum o of
            Left _          -> return False
            Right (Datum e) -> case PlutusTx.fromBuiltinData e of
                Nothing -> return False
                Just d@InheritDatum{..}
                    | beneficiary == _bene && _own == owner  -> return True
                    | otherwise                                           -> return False
        _           -> return False

endpoints :: Contract () InheritSchema Text ()
endpoints = awaitPromise (close' `select` inherit' `select` takeTheReward') >> endpoints
  where
    inherit' = endpoint @"Inherit" inherit
    close' = endpoint @"close" close
    takeTheReward' = endpoint @"Retrieve" $ retrieve

mkSchemaDefinitions ''InheritSchema

mkKnownCurrencies []
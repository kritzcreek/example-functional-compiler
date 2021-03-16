module Backend.Syntax where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Partial.Unsafe (unsafeCrashWith)

newtype VName = VName String
derive newtype instance eqV :: Eq VName
derive newtype instance ordV :: Ord VName
derive instance genericVName :: Generic VName _
instance showVName :: Show VName where
  show x = genericShow x

newtype CName = CName String
derive newtype instance eqC :: Eq CName
derive newtype instance ordC :: Ord CName
derive instance genericCName :: Generic CName _
instance showCName :: Show CName where
  show x = genericShow x

data Index = Fst | Snd

derive instance genericIndex :: Generic Index _
instance showIndex :: Show Index where
  show x = genericShow x

data Term
  = LetVal VName Value Term
  -- letcont k x = K in L
  | LetCont CName VName Term Term
  | Proj VName Index VName Term
  | AppCont CName VName
  | AppFn VName CName VName
  -- case x of k1 | k2
  | Case VName CName CName

derive instance genericTerm :: Generic Term _
instance showTerm :: Show Term where
  show x = genericShow x

data Value
  = Unit
  | Pair Value Value
  | Inj Index Value
  | Lam CName VName Term

derive instance genericValue :: Generic Value _
instance showValue :: Show Value where
  show x = genericShow x

data RTValue
  = RTUnit
  | RTPair RTValue RTValue
  | RTInj Index RTValue
  | RTCont CName RTClosure

derive instance genericRTValue :: Generic RTValue _
instance showRTValue :: Show RTValue where
  show x = genericShow x

data RTClosure = Cls Env VName Term | Halt

derive instance genericRTClosure :: Generic RTClosure _
instance showRTClosure :: Show RTClosure where
  show x = genericShow x

type Env =
  { vals :: Map VName RTValue
  , conts :: Map CName RTClosure
  }

lookupVal :: VName -> Env -> RTValue
lookupVal v e = case Map.lookup v e.vals of
  Just x -> x
  Nothing -> unsafeCrashWith $ "Failed to look up value" <> show v

lookupCont :: CName -> Env -> RTClosure
lookupCont c e = case Map.lookup c e.conts of
  Just x -> x
  _ -> unsafeCrashWith $ "Failed to look up continuation" <> show c

evalVal :: Env -> Value -> RTValue
evalVal env = case _ of
  Unit -> RTUnit
  Pair x y -> RTPair (evalVal env x) (evalVal env y)
  Inj ix x -> RTInj ix (evalVal env x)
  Lam k x b -> RTCont k (Cls env x b)

evalTerm :: Env -> Term -> Term
evalTerm env = case _ of
  LetVal x v k ->
    let evaled = evalVal env v in
    let newEnv = env { vals = Map.insert x evaled env.vals } in
    evalTerm newEnv k
  LetCont c x k l ->
    let closure = Cls env x k in
    let newEnv = env { conts = Map.insert c closure env.conts } in
    evalTerm newEnv l
  Proj y ix x k -> do
    let
      projected = case Map.lookup x env.vals of
        Just (RTPair x1 x2) -> case ix of
          Fst -> x1
          Snd -> x2
        _ -> unsafeCrashWith "Failed to look up pair"
      newEnv = env { vals = Map.insert y projected env.vals }
    evalTerm newEnv k
  AppCont k x -> case lookupCont k env of
    Cls env' y t -> do
       let xVal = lookupVal x env
       let newEnv = env' { vals = Map.insert y xVal env'.vals }
       evalTerm newEnv t
    Halt ->
      unsafeCrashWith (show (lookupVal x env))

  AppFn f k x -> case lookupVal f env of
    RTCont j (Cls env' y upK) -> do
      let
        newEnv = env'
          { vals = Map.insert y (lookupVal x env) env'.vals
          , conts = Map.insert j (lookupCont k env) env'.conts
          }
      evalTerm newEnv upK
    _ -> unsafeCrashWith "failed to lookup fn"
  Case x k1 k2 -> do
    let
      { k, r } = case lookupVal x env of
        (RTInj Fst r) -> { k: k1, r }
        (RTInj Snd r) -> { k: k2, r }
        _ -> unsafeCrashWith "Failed to lookup inj"
    case lookupCont k env of
      Cls env' y t -> do
        let newEnv = env' { vals = Map.insert y r env'.vals }
        evalTerm newEnv t
      Halt ->
        unsafeCrashWith (show r)

execTerm :: Term -> Term
execTerm = evalTerm { vals: Map.empty, conts: Map.singleton (cn "halt") Halt }

vn = VName
cn = CName
selfid =
  LetVal
    (vn "id") (Lam (cn "k") (vn "x") (AppCont (cn "k") (vn "x")))
    (AppFn (vn "id") (cn "halt") (vn "id"))

selfid2 =
  LetVal
    (vn "id1") (Lam (cn "k") (vn "x") (AppCont (cn "k") (vn "x")))
    (LetVal
      (vn "id2") (Lam (cn "k") (vn "y") (AppCont (cn "k") (vn "y")))
      (AppFn (vn "id2") (cn "halt") (vn "id1")))

tuplesFst =
  LetVal
    (vn "tpl") (Pair Unit (Pair Unit Unit))
    (Proj (vn "fst") Fst (vn "tpl")
     (AppCont (cn "halt") (vn "fst")))

tuplesSnd =
  LetVal
    (vn "tpl") (Pair Unit (Pair Unit Unit))
    (Proj (vn "snd") Snd (vn "tpl")
     (AppCont (cn "halt") (vn "snd")))

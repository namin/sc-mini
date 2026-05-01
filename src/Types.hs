module Types where

import Data (Name)

-- Monomorphic type expressions. SLL is first-order with no polymorphism,
-- so a type is just a nullary type constructor.
data Type = TyCon Name deriving (Eq, Show)

-- A constructor declaration: name and field types, in order.
-- e.g. CtrDef "S" [TyCon "Nat"], CtrDef "Cons" [TyCon "Sym", TyCon "LSym"]
data CtrDef = CtrDef Name [Type] deriving (Eq, Show)

-- A data type declaration: type name and its constructors.
data DataDef = DataDef Name [CtrDef] deriving (Eq, Show)

-- Function signature: argument types and return type.
type Signature = ([Type], Type)

-- Type environment for an SLL program: data declarations plus
-- per-function signatures. Lookup-only; no inference.
data TypeEnv = TypeEnv
  { typeDefs :: [DataDef]
  , funSigs  :: [(Name, Signature)]
  } deriving (Eq, Show)

-- Lookups. Caller is responsible for the result existing; an absent
-- key signals a malformed program for our purposes.
lookupSig :: Name -> TypeEnv -> Maybe Signature
lookupSig n env = lookup n (funSigs env)

lookupDataDef :: Name -> TypeEnv -> Maybe DataDef
lookupDataDef n env = go (typeDefs env)
  where
    go [] = Nothing
    go (d@(DataDef tn _) : ds) | tn == n = Just d
                                | otherwise = go ds

-- Find the type that a constructor belongs to.
ctrType :: Name -> TypeEnv -> Maybe Type
ctrType cn env = go (typeDefs env)
  where
    go [] = Nothing
    go (DataDef tn ctrs : ds)
      | any (\(CtrDef c _) -> c == cn) ctrs = Just (TyCon tn)
      | otherwise = go ds

-- Find a constructor's declared field types.
ctrFields :: Name -> TypeEnv -> Maybe [Type]
ctrFields cn env = go (typeDefs env)
  where
    go [] = Nothing
    go (DataDef _ ctrs : ds) =
      case [ts | CtrDef c ts <- ctrs, c == cn] of
        (ts:_) -> Just ts
        []     -> go ds

module LeanEmbed
  ( embedProgram
  , embedExpr
  , embedConjecture
  ) where

import Data
import Types

import Data.List (intercalate, nub)
import qualified Data.Graph as Graph
import Data.Graph (SCC(..))

-- =========================================================================
-- Type and constructor rendering
-- =========================================================================

-- Lean type name. We append a prime to dodge clashes with Lean's stdlib
-- (Nat, Bool, List, ...). The prime is purely cosmetic.
renderType :: Type -> String
renderType (TyCon n) = n ++ "'"

-- inductive Foo' where
--   | C1 : Foo'
--   | C2 : T1 -> T2 -> Foo'
renderDataDef :: DataDef -> String
renderDataDef (DataDef tn ctrs) =
  unlines $ ("inductive " ++ tn ++ "' where") : map renderCtr ctrs
  where
    renderCtr (CtrDef cn fields) =
      "  | " ++ cn ++ " : " ++
      concatMap (\t -> renderType t ++ " -> ") fields ++
      tn ++ "'"

-- =========================================================================
-- Expression rendering
-- =========================================================================

-- Always parenthesize compound terms so they nest safely as arguments.
-- Outer callers can strip the outermost parens if cosmetics matter.
renderExpr :: Expr -> String
renderExpr (Var n)            = n
renderExpr (Ctr cn [])        = "(." ++ cn ++ ")"
renderExpr (Ctr cn es)        = "(." ++ cn ++ " " ++ unwords (map renderExpr es) ++ ")"
renderExpr (FCall fn es)      = "(" ++ fn ++ " " ++ unwords (map renderExpr es) ++ ")"
renderExpr (GCall gn es)      = "(" ++ gn ++ " " ++ unwords (map renderExpr es) ++ ")"
renderExpr (Let (v, e1) e2)   =
  "(let " ++ v ++ " := " ++ renderExpr e1 ++ "; " ++ renderExpr e2 ++ ")"

-- Public: TypeEnv arg reserved for future use (e.g. inserting type
-- ascriptions to disambiguate the anonymous .C constructor syntax).
embedExpr :: TypeEnv -> Expr -> String
embedExpr _ = renderExpr

-- =========================================================================
-- Function rendering
-- =========================================================================

-- An f-function is a single equation: render directly as `def f a b : T := body`.
renderFDef :: TypeEnv -> FDef -> String
renderFDef env (FDef fn args body) =
  case lookupSig fn env of
    Nothing -> error $ "LeanEmbed: no signature for f-function " ++ fn
    Just (argTys, retTy)
      | length argTys /= length args ->
          error $ "LeanEmbed: arity mismatch for " ++ fn
      | otherwise ->
          let typedArgs = zipWith typedBinder args argTys
              header    = "def " ++ fn ++ concatMap (" " ++) typedArgs
                          ++ " : " ++ renderType retTy ++ " :="
          in header ++ "\n  " ++ renderExpr body

typedBinder :: Name -> Type -> String
typedBinder n t = "(" ++ n ++ " : " ++ renderType t ++ ")"

-- A g-function is a list of clauses sharing a name. We emit one `def` whose
-- body matches on a fresh scrutinee variable, with one arm per clause.
-- Trailing arg names are taken from the first clause (SLL convention: all
-- clauses of a g-function use the same names for non-scrutinee args).
renderGFun :: TypeEnv -> Name -> [GDef] -> String
renderGFun _   name []          = error $ "LeanEmbed: empty g-function group for " ++ name
renderGFun env name clauses@(GDef _ _ tailNames _ : _) =
  case lookupSig name env of
    Nothing -> error $ "LeanEmbed: no signature for g-function " ++ name
    Just (argTys, retTy) -> case argTys of
      [] -> error $ "LeanEmbed: g-function " ++ name ++ " has no scrutinee"
      (scrutTy : tailTys)
        | length tailTys /= length tailNames ->
            error $ "LeanEmbed: arity mismatch for " ++ name
        | otherwise ->
            let scrutName  = freshScrutinee tailNames clauses
                headBinders = typedBinder scrutName scrutTy
                            : zipWith typedBinder tailNames tailTys
                arms = map renderArm clauses
                body = "  match " ++ scrutName ++ " with\n"
                       ++ unlines (map ("  " ++) arms)
            in "def " ++ name ++ concatMap (" " ++) headBinders
               ++ " : " ++ renderType retTy ++ " :=\n" ++ body

renderArm :: GDef -> String
renderArm (GDef _ (Pat cn pvs) _ body) =
  "| ." ++ cn ++ concatMap (" " ++) pvs ++ " => " ++ renderExpr body

-- Pick a scrutinee name that doesn't collide with any tail-arg name or any
-- pattern variable in any clause. `_x` is the usual first try.
freshScrutinee :: [Name] -> [GDef] -> Name
freshScrutinee tailNames clauses =
  let used = tailNames ++ concatMap clauseVars clauses
      candidates = "_x" : ["_x" ++ show i | i <- [(1::Int)..]]
  in head [c | c <- candidates, c `notElem` used]
  where
    clauseVars (GDef _ (Pat _ pvs) _ _) = pvs

-- =========================================================================
-- Mutual recursion via SCCs
-- =========================================================================

-- A "decl" is one renderable unit: an FDef or a group of GDefs sharing a name.
data Decl = DeclF FDef | DeclG Name [GDef]

declName :: Decl -> Name
declName (DeclF (FDef n _ _))     = n
declName (DeclG n _)              = n

declCallees :: Decl -> [Name]
declCallees (DeclF (FDef _ _ b))  = nub (calleesExpr b)
declCallees (DeclG _ gs)          = nub (concatMap (\(GDef _ _ _ b) -> calleesExpr b) gs)

calleesExpr :: Expr -> [Name]
calleesExpr (Var _)            = []
calleesExpr (Ctr _ es)         = concatMap calleesExpr es
calleesExpr (FCall n es)       = n : concatMap calleesExpr es
calleesExpr (GCall n es)       = n : concatMap calleesExpr es
calleesExpr (Let (_, e1) e2)   = calleesExpr e1 ++ calleesExpr e2

-- Group g-function clauses by name, preserving first-seen order.
groupGDefs :: [GDef] -> [(Name, [GDef])]
groupGDefs = foldr step []
  where
    step g@(GDef n _ _ _) acc =
      case break (\(m, _) -> m == n) acc of
        (pre, (m, gs):post) -> pre ++ (m, g : gs) : post
        (_, [])             -> acc ++ [(n, [g])]

programDecls :: Program -> [Decl]
programDecls (Program fs gs) =
  map DeclF fs ++ map (uncurry DeclG) (groupGDefs gs)

-- SCCs in reverse topological order: dependencies appear first.
sccs :: Program -> [SCC Decl]
sccs p =
  let ds    = programDecls p
      keys  = map declName ds
      nodes = [(d, declName d, filter (`elem` keys) (declCallees d)) | d <- ds]
  in Graph.stronglyConnComp nodes

renderDecl :: TypeEnv -> Decl -> String
renderDecl env (DeclF fd)    = renderFDef env fd
renderDecl env (DeclG n gs)  = renderGFun env n gs

renderSCC :: TypeEnv -> SCC Decl -> String
renderSCC env (AcyclicSCC d) = renderDecl env d
renderSCC env (CyclicSCC [d]) = renderDecl env d
renderSCC env (CyclicSCC ds)  =
  "mutual\n" ++ intercalate "\n" (map (renderDecl env) ds) ++ "\nend"

-- =========================================================================
-- Program embedding
-- =========================================================================

-- Full Program.lean: inductive types, then defs in dependency order.
embedProgram :: TypeEnv -> Program -> String
embedProgram env p =
  let datas = unlines (map renderDataDef (typeDefs env))
      defs  = intercalate "\n\n" (map (renderSCC env) (sccs p))
  in datas ++ "\n" ++ defs ++ "\n"

-- =========================================================================
-- Conjecture embedding
-- =========================================================================

-- Walk an Expr to gather (var, type) pairs from typed use sites: function
-- args and constructor fields. Bare `Var` occurrences contribute nothing.
varTypesAt :: TypeEnv -> Expr -> [(Name, Type)]
varTypesAt _   (Var _)         = []
varTypesAt env (Ctr cn es)     =
  case ctrFields cn env of
    Nothing -> error $ "LeanEmbed: unknown constructor " ++ cn
    Just ts -> bind ts es ++ concatMap (varTypesAt env) es
varTypesAt env (FCall fn es)   = atCall fn es env
varTypesAt env (GCall gn es)   = atCall gn es env
varTypesAt env (Let (_, e1) e2) = varTypesAt env e1 ++ varTypesAt env e2

atCall :: Name -> [Expr] -> TypeEnv -> [(Name, Type)]
atCall fn es env =
  case lookupSig fn env of
    Nothing -> error $ "LeanEmbed: unknown function " ++ fn
    Just (ats, _) -> bind ats es ++ concatMap (varTypesAt env) es

bind :: [Type] -> [Expr] -> [(Name, Type)]
bind ts es = [(v, t) | (Var v, t) <- zip es ts]

-- Properly scoped free variables: a Let binder removes its name from the
-- body's free set. (DataUtil.vnames does not, so we don't reuse it here.)
freeNames :: Expr -> [Name]
freeNames = nub . go
  where
    go (Var v)            = [v]
    go (Ctr _ es)         = concatMap go es
    go (FCall _ es)       = concatMap go es
    go (GCall _ es)       = concatMap go es
    go (Let (v, e1) e2)   = go e1 ++ filter (/= v) (go e2)

-- Free vars of `e ∪ e'`, each tagged with the type inferred from at least
-- one use site. Order: first-appearance in `e`, then any new ones in `e'`.
freeVarTypes :: TypeEnv -> Expr -> Expr -> [(Name, Type)]
freeVarTypes env e e' =
  let names = nub (freeNames e ++ freeNames e')
      uses  = varTypesAt env e ++ varTypesAt env e'
      lookupT n = case lookup n uses of
        Just t  -> (n, t)
        Nothing -> error $ "LeanEmbed: cannot infer type of free variable " ++ n
  in map lookupT names

-- Conjecture.lean: imports the prebuilt Program module, then asserts
-- the LLM-proposed equivalence under the given proof body.
embedConjecture
  :: TypeEnv
  -> Program  -- not directly used here; reserved for future (e.g. ad-hoc lemmas)
  -> Expr     -- e (current configuration)
  -> Expr     -- e' (proposed generalization)
  -> String   -- proof body, e.g. "by intros; simp_all [gAdd, gMult]"
  -> String
embedConjecture env _ e e' proof =
  let fvs     = freeVarTypes env e e'
      binders = unwords [typedBinder v t | (v, t) <- fvs]
      forall_ = if null fvs then "" else "forall " ++ binders ++ ", "
      lhs     = renderExpr e
      rhs     = renderExpr e'
  in unlines
       [ "import Program"
       , ""
       , "theorem gen_ok : " ++ forall_ ++ lhs ++ " = " ++ rhs ++ " :="
       , "  " ++ proof
       ]

module DataUtil(
  isValue,isCall,isVar,size,
  fDef, gDef, gDefs,
  (//), renaming, vnames,nameSupply,
  nodeLabel,isRepeated,unused,
  homeEmbed, msg
  ) where

import Data
import Data.Maybe
import Data.Char
import Data.List

isValue :: Expr -> Bool
isValue (Ctr _ args) = and $ map isValue args
isValue _ = False

isCall :: Expr -> Bool
isCall (FCall _ _) = True
isCall (GCall _ _) = True
isCall _ = False

isVar :: Expr -> Bool
isVar (Var _) = True
isVar _ = False

fDef :: Program -> Name -> FDef
fDef (Program fs _) fname = head [f | f@(FDef x _ _) <- fs, x == fname]

gDefs :: Program -> Name -> [GDef]
gDefs (Program _ gs) gname = [g | g@(GDef x _ _ _) <- gs, x == gname]

gDef :: Program -> Name -> Name -> GDef
gDef p gname cname = head [g | g@(GDef _ (Pat c _) _ _) <- gDefs p gname, c == cname]

(//) :: Expr -> Subst -> Expr
(Var x) // sub = maybe (Var x) id (lookup x sub)
(Ctr name args) // sub = Ctr name (map (// sub) args)
(FCall name args) // sub = FCall name (map (// sub) args)
(GCall name args) // sub = GCall name (map (// sub) args)
(Let (x, e1) e2) // sub  = Let (x, (e1 // sub)) (e2 // sub)

nameSupply :: NameSupply
nameSupply = ["v" ++ (show i) | i <- [1 ..] ]

unused :: Contract -> NameSupply -> NameSupply
unused (Contract _ (Pat _ vs)) = (\\ vs)

vnames :: Expr -> [Name]
vnames = nub . vnames'

vnames' :: Expr -> [Name]
vnames' (Var v) = [v]
vnames' (Ctr _ args)   = concat $ map vnames' args
vnames' (FCall _ args) = concat $ map vnames' args
vnames' (GCall _ args) = concat $ map vnames' args
vnames' (Let (_, e1) e2) = vnames' e1 ++ vnames' e2

isRepeated :: Name -> Expr -> Bool
isRepeated vn e = (length $ filter (== vn) (vnames' e)) > 1

renaming :: Expr -> Expr -> Maybe Renaming
renaming e1 e2 = f $ partition isNothing $ renaming' (e1, e2) where
  f (x:_, _) = Nothing
  f (_, ps) = g gs1 gs2
    where
      gs1 = groupBy (\(a, b) (c, d) -> a == c) $ sortBy h $ nub $ catMaybes ps
      gs2 = groupBy (\(a, b) (c, d) -> b == d) $ sortBy h $ nub $ catMaybes ps
      h (a, b) (c, d) = compare a c
  g xs ys = if all ((== 1) . length) xs && all ((== 1) . length) ys
    then Just (concat xs) else Nothing

renaming' :: (Expr, Expr) -> [Maybe (Name, Name)]
renaming' ((Var x), (Var y)) = [Just (x, y)]
renaming' ((Ctr n1 args1), (Ctr n2 args2)) | n1 == n2 = concat $ map renaming' $ zip args1 args2
renaming' ((FCall n1 args1), (FCall n2 args2)) | n1 == n2 = concat $ map renaming' $ zip args1 args2
renaming' ((GCall n1 args1), (GCall n2 args2)) | n1 == n2 = concat $ map renaming' $ zip args1 args2
renaming' (Let (v, e1) e2, Let (v', e1') e2') = renaming' (e1, e1') ++ renaming' (e2, e2' // [(v, Var v')])
renaming' _  = [Nothing]

-- Homeomorphic embedding: e1 ◁ e2 means e1 is structurally simpler than e2.
-- Used as the whistle: if an ancestor embeds in the current term, the term is growing.
homeEmbed :: Expr -> Expr -> Bool
homeEmbed (Var _) _ = True
homeEmbed e1 e2 | couple e1 e2 = True
homeEmbed e1 e2 = dive e1 e2

couple :: Expr -> Expr -> Bool
couple (Ctr n1 args1) (Ctr n2 args2) =
  n1 == n2 && length args1 == length args2 && and (zipWith homeEmbed args1 args2)
couple (FCall n1 args1) (FCall n2 args2) =
  n1 == n2 && length args1 == length args2 && and (zipWith homeEmbed args1 args2)
couple (GCall n1 args1) (GCall n2 args2) =
  n1 == n2 && length args1 == length args2 && and (zipWith homeEmbed args1 args2)
couple _ _ = False

dive :: Expr -> Expr -> Bool
dive e1 (Ctr _ args)   = any (homeEmbed e1) args
dive e1 (FCall _ args) = any (homeEmbed e1) args
dive e1 (GCall _ args) = any (homeEmbed e1) args
dive e1 (Let (_, a) b) = homeEmbed e1 a || homeEmbed e1 b
dive _ _ = False

-- Most-specific generalization of two expressions.
-- Returns (generalized_expr, subst_for_e1, subst_for_e2).
-- The generalized expr with subst1 applied gives e1, with subst2 gives e2.
msg :: NameSupply -> Expr -> Expr -> (Expr, Subst, Subst)
msg ns (Ctr c1 args1) (Ctr c2 args2)
  | c1 == c2, length args1 == length args2 =
      let (args', s1s, s2s) = msgList ns args1 args2
      in (Ctr c1 args', concat s1s, concat s2s)
msg ns (FCall f1 args1) (FCall f2 args2)
  | f1 == f2, length args1 == length args2 =
      let (args', s1s, s2s) = msgList ns args1 args2
      in (FCall f1 args', concat s1s, concat s2s)
msg ns (GCall g1 args1) (GCall g2 args2)
  | g1 == g2, length args1 == length args2 =
      let (args', s1s, s2s) = msgList ns args1 args2
      in (GCall g1 args', concat s1s, concat s2s)
msg ns (Var v1) (Var v2) | v1 == v2 = (Var v1, [], [])
msg (n:_) e1 e2 = (Var n, [(n, e1)], [(n, e2)])

msgList :: NameSupply -> [Expr] -> [Expr] -> ([Expr], [Subst], [Subst])
msgList ns [] [] = ([], [], [])
msgList ns (a:as) (b:bs) =
  let (g, s1, s2) = msg ns a b
      usedNames = map fst s1
      ns' = filter (`notElem` usedNames) ns
      (gs, s1s, s2s) = msgList ns' as bs
  in (g:gs, s1:s1s, s2:s2s)

size :: Expr -> Integer
size (Var _) = 1
size (Ctr _ args) = 1 + sum (map size args)
size (FCall _ args) = 1 + sum (map size args)
size (GCall _ args) = 1 + sum (map size args)
size (Let (_, e1) e2) = 1 + (size e1) + (size e2)

nodeLabel :: Node a -> a
nodeLabel (Node l _) = l

step :: Node a -> Step (Graph a)
step (Node _ s) = s

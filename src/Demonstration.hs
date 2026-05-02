{-# LANGUAGE QuasiQuotes #-}

module Demonstration where

import Data
import DataUtil
import DataIO
import Driving
import Interpreter
import TreeInterpreter
import Supercompiler
import Folding
import Data.List
import Data.Maybe
import Generator
import Prototype
import Deforester
import Types

prog1 :: Program
prog1 = [prog|
  gAdd(Z(), y) = y;
  gAdd(S(x), y) = S(gAdd(x, y));
  gMult(Z(), y) = Z();
  gMult(S(x), y) = gAdd(y, gMult(x, y));
  fSqr(x) = gMult(x, x);
  gEven(Z()) = True();
  gEven(S(x)) = gOdd(x);
  gOdd(Z()) = False();
  gOdd(S(x)) = gEven(x);
  gAdd1(Z(), y) = y;
  gAdd1(S(x), y) = gAdd1(x, S(y));
|]

prog1Types :: TypeEnv
prog1Types = TypeEnv
  { typeDefs =
      [ DataDef "Nat"  [CtrDef "Z" [], CtrDef "S" [TyCon "Nat"]]
      , DataDef "Bool" [CtrDef "True" [], CtrDef "False" []]
      ]
  , funSigs =
      [ ("gAdd",  ([TyCon "Nat", TyCon "Nat"], TyCon "Nat"))
      , ("gMult", ([TyCon "Nat", TyCon "Nat"], TyCon "Nat"))
      , ("fSqr",  ([TyCon "Nat"], TyCon "Nat"))
      , ("gEven", ([TyCon "Nat"], TyCon "Bool"))
      , ("gOdd",  ([TyCon "Nat"], TyCon "Bool"))
      , ("gAdd1", ([TyCon "Nat", TyCon "Nat"], TyCon "Nat"))
      ]
  , funPartial = []
  }

prog2 :: Program
prog2 = [prog|
  gEqSymb(A(), y) = gEqA(y);
  gEqSymb(B(), y) = gEqB(y);
  gEqA(A()) = True();  gEqA(B()) = False();
  gEqB(A()) = False(); gEqB(B()) = True();
  gIf(True(), x, y) = x;
  gIf(False(), x, y) = y;
  fMatch(p, s) = gM(p, s, p, s);
  gM(Nil(), ss, op, os) = True();
  gM(Cons(p, pp), ss, op, os) = gX(ss, p, pp, op, os);
  gX(Nil(), p, pp,  op, os) = False();
  gX(Cons(s, ss), p, pp,  op, os) = gIf(gEqSymb(p, s), gM(pp, ss, op, os), gN(os, op));
  gN(Nil(), op) = False();
  gN(Cons(s, ss), op) = gM(op, ss, op, ss);
|]

-- gIf is monomorphic-per-program; in prog2 it's used at Bool only
-- (both branches return Bool from gM/gN), so we type it that way.
prog2Types :: TypeEnv
prog2Types = TypeEnv
  { typeDefs =
      [ DataDef "Sym"  [CtrDef "A" [], CtrDef "B" []]
      , DataDef "Bool" [CtrDef "True" [], CtrDef "False" []]
      , DataDef "LSym" [CtrDef "Nil" [], CtrDef "Cons" [TyCon "Sym", TyCon "LSym"]]
      ]
  , funSigs =
      [ ("gEqSymb", ([TyCon "Sym", TyCon "Sym"], TyCon "Bool"))
      , ("gEqA",    ([TyCon "Sym"], TyCon "Bool"))
      , ("gEqB",    ([TyCon "Sym"], TyCon "Bool"))
      , ("gIf",     ([TyCon "Bool", TyCon "Bool", TyCon "Bool"], TyCon "Bool"))
      , ("fMatch",  ([TyCon "LSym", TyCon "LSym"], TyCon "Bool"))
      , ("gM",      ([TyCon "LSym", TyCon "LSym", TyCon "LSym", TyCon "LSym"], TyCon "Bool"))
      , ("gX",      ([TyCon "LSym", TyCon "Sym", TyCon "LSym", TyCon "LSym", TyCon "LSym"], TyCon "Bool"))
      , ("gN",      ([TyCon "LSym", TyCon "LSym"], TyCon "Bool"))
      ]
  -- gM/gX/gN are mutually recursive without a structurally decreasing
  -- measure (gN restarts from the original pattern). Lean can't infer
  -- termination automatically, so we declare them partial. Our
  -- auto-prove (`simp_all` with no defs) only needs let-elimination,
  -- not function unfolding, so partial is fine for verification.
  , funPartial = ["gM", "gX", "gN"]
  }

-- more clear KMP test
prog2a :: Program
prog2a = [prog|
  gEqSymb(A(), y) = gEqA(y);
  gEqSymb(B(), y) = gEqB(y);
  gEqA(A()) = True();  gEqA(B()) = False();
  gEqB(A()) = False(); gEqB(B()) = True();
  gIf(True(), x, y) = x;
  gIf(False(), x, y) = y;
  fMatch(p, s) = gM(p, s, p, s);
  gM(Nil(), ss, op, os) = True();
  gM(Cons(p, pp), ss, op, os) = gX(ss, p, pp, op, os);
  gX(Nil(), p, pp,  op, os) = False();
  gX(Cons(s, ss), p, pp,  op, os) = gIf(gEqSymb(p, s), gM(pp, ss, op, os), gN(os, op));
  gN(Nil(), op) = False();
  gN(Cons(s, ss), op) = gM(op, ss, op, ss);
|]

prog2aTypes :: TypeEnv
prog2aTypes = prog2Types

prog3 :: Program
prog3 = [prog|
  gAdd(Z(), y) = y;
  gAdd(S(x), y) = S(gAdd(x, y));
  gDouble(Z()) = Z();
  gDouble(S(x)) = S(S(gDouble(x)));
  gHalf(Z()) = Z();
  gHalf(S(x)) = gHalf1(x);
  gHalf1(Z()) = Z();
  gHalf1(S(x)) = S(gHalf(x));
  gEq(Z(), y) = gEqZ(y);
  gEq(S(x), y) = gEqS(y, x);
  gEqZ(Z()) = True();
  gEqZ(S(x)) = False();
  gEqS(Z(), x) = False();
  gEqS(S(y), x) = gEq(x, y);
|]

prog3Types :: TypeEnv
prog3Types = TypeEnv
  { typeDefs =
      [ DataDef "Nat"  [CtrDef "Z" [], CtrDef "S" [TyCon "Nat"]]
      , DataDef "Bool" [CtrDef "True" [], CtrDef "False" []]
      ]
  , funSigs =
      [ ("gAdd",    ([TyCon "Nat", TyCon "Nat"], TyCon "Nat"))
      , ("gDouble", ([TyCon "Nat"], TyCon "Nat"))
      , ("gHalf",   ([TyCon "Nat"], TyCon "Nat"))
      , ("gHalf1",  ([TyCon "Nat"], TyCon "Nat"))
      , ("gEq",     ([TyCon "Nat", TyCon "Nat"], TyCon "Bool"))
      , ("gEqZ",    ([TyCon "Nat"], TyCon "Bool"))
      , ("gEqS",    ([TyCon "Nat", TyCon "Nat"], TyCon "Bool"))
      ]
  , funPartial = []
  }

prog4 :: Program
prog4 = [prog|
  fInf() = S(fInf());
  fB(x) = fB(S(x));
|]

-- A list module: lists of Nat with append, reverse, length, sum.
-- Larger surface than the existing demo programs (5 g-functions on
-- two types), with classic functor/monoid identities the LLM can
-- target as eureka lemmas.
prog5 :: Program
prog5 = [prog|
  gAdd(Z(), y) = y;
  gAdd(S(x), y) = S(gAdd(x, y));
  gAppend(Nil(), ys) = ys;
  gAppend(Cons(x, xs), ys) = Cons(x, gAppend(xs, ys));
  gReverse(Nil()) = Nil();
  gReverse(Cons(x, xs)) = gAppend(gReverse(xs), Cons(x, Nil()));
  gLength(Nil()) = Z();
  gLength(Cons(x, xs)) = S(gLength(xs));
  gSum(Nil()) = Z();
  gSum(Cons(x, xs)) = gAdd(x, gSum(xs));
|]

prog5Types :: TypeEnv
prog5Types = TypeEnv
  { typeDefs =
      [ DataDef "Nat"  [CtrDef "Z" [], CtrDef "S" [TyCon "Nat"]]
      , DataDef "LNat" [CtrDef "Nil" [], CtrDef "Cons" [TyCon "Nat", TyCon "LNat"]]
      ]
  , funSigs =
      [ ("gAdd",     ([TyCon "Nat", TyCon "Nat"], TyCon "Nat"))
      , ("gAppend",  ([TyCon "LNat", TyCon "LNat"], TyCon "LNat"))
      , ("gReverse", ([TyCon "LNat"], TyCon "LNat"))
      , ("gLength",  ([TyCon "LNat"], TyCon "Nat"))
      , ("gSum",     ([TyCon "LNat"], TyCon "Nat"))
      ]
  , funPartial = []
  }

-- counting steps of interpreter
demo01 =
  intC prog1 [expr|gEven(fSqr(S(S(Z()))))|]

-- int and eval produce the same values
demo02 =
  int prog1 [expr|gEven(fSqr(S(S(Z()))))|]
demo03 =
  eval prog1 [expr|gEven(fSqr(S(S(Z()))))|]
demo04 =
  int prog1 [expr|fSqr(S(S(Z())))|]
demo05 =
  eval prog1 [expr|fSqr(S(S(Z())))|]

-- trying interpret undefined expression
demo06 =
  int  prog1 [expr|fSqr(S(S(x)))|]

-- trying eval undefined expression
demo07 =
  eval prog1 [expr|fSqr(S(S(x)))|]

-- "interpret" infinite number
demo08 =
  int  prog4 [expr|fInf()|]

-- "eval" infinite number
demo09 =
  eval prog4 [expr|fInf()|]

--   driving (variants)
demo10 =
  (driveMachine prog1) nameSupply [expr|gOdd(gAdd(x, gMult(x, S(x))))|]

-- driving (transient step)
demo11 =
  (driveMachine prog1) nameSupply [expr|gOdd(S(gAdd(v1, gMult(x, S(x)))))|]

-- building infinite tree
demo12 =
  putStrLn $ printTree $ buildTree (driveMachine prog1) [expr|gEven(fSqr(x))|]

-- using intTree (infinite tree) to run task
demo13 =
  intTree (buildTree (driveMachine prog1) [expr|gEven(fSqr(x))|]) [("x", [expr|S(S(Z()))|])]

-- using intTree (folded finite graph) to run task
demo13a =
  intTree (foldTree $ buildTree (driveMachine prog1) [expr|gEven(fSqr(x))|]) [("x", [expr|S(S(Z()))|])]

-- using intTree (infinite tree) to run task
demo14 =
  intTree (buildTree (driveMachine prog1) [expr|gEven(fSqr(x))|]) [("x", [expr|S(S(S(Z())))|])]

-- successful folding
demo15 =
  putStrLn $ printTree $ foldTree $ buildTree (driveMachine prog1) [expr|gEven(fSqr(x))|]

-- an example of "not foldable" tree
demo16 =
  putStrLn $ printTree $ foldTree $ buildTree (driveMachine prog1) [expr|gAdd1(x, y)|]

-- an example of generalization, set sizeBound = 5 to get the same result as in the paper
demo17 =
  putStrLn $ printTree $ foldTree $ buildFTree (driveMachine prog1) [expr|gAdd1(x, y)|]

-- even/sqr - just transformation
demo18 = do
  let (c2, p2) = transform ([expr|gEven(fSqr(x))|], prog1)
  putStrLn "\ntransformation:\n"
  putStrLn (show c2)
  putStrLn (show p2)

-- even/sqr - deforestation
demo19 = do
  let (c2, p2) = deforest ([expr|gEven(fSqr(x))|], prog1)
  putStrLn "\ndeforestation:\n"
  putStrLn (show c2)
  putStrLn (show p2)

-- even/sqr - supercompilation
demo20 = do
  let (c2, p2) = supercompile ([expr|gEven(fSqr(x))|], prog1)
  putStrLn "supercompilation:\n"
  putStrLn (show c2)
  putStrLn (show p2)

-- KMP -- transform -- graph
demo21 =
  putStrLn $ printTree $ foldTree $ buildFTree (driveMachine prog2) conf2

-- KMP -- deforest -- graph
demo22 =
  putStrLn $ printTree $ simplify $ foldTree $ buildFTree (driveMachine prog2) conf2

-- KMP -- supercompile -- graph
demo23 =
  putStrLn $ printTree $ foldTree $ buildFTree (addPropagation (driveMachine prog2)) conf2

g = simplify $ foldTree $ buildFTree (addPropagation (driveMachine prog2)) conf2

demo24 = do
  let (c2, p2) = residuate g
  putStrLn (show c2)
  putStrLn (show p2)

-- KMP - transformation
demo25 = do
  let (c2, p2) = transform (conf2, prog2)
  putStrLn (show c2)
  putStrLn (show p2)

-- KMP - deforestation
demo26 = do
  let (c2, p2) = deforest (conf2, prog2)
  putStrLn (show c2)
  putStrLn (show p2)

-- KMP - supercompilation
demo27 = do
  let (c2, p2) = supercompile (conf2, prog2)
  putStrLn (show c2)
  putStrLn (show p2)

-- "program analysis"
demo30 = do
  let (c2, p2) = supercompile ([expr|gAdd(gAdd(x, y), z)|], prog1)
  putStrLn (show c2)
  putStrLn (show p2)

demo31 = do
  let (c2, p2) = supercompile ([expr|gAdd(x, gAdd(y, z))|], prog1)
  putStrLn (show c2)
  putStrLn (show p2)

-- supercompiled eqpressions are equal =>
-- original expressions are equivalent
demo32 =
  supercompile ([expr|gAdd(x, gAdd(y, z))|], prog1) == supercompile ([expr|gAdd(gAdd(x, y), z)|], prog1)

demo33 = do
  let (c2, p2) = supercompile ([expr|gEq(gHalf(gDouble(n)),n)|], prog3)
  putStrLn "supercompilation:\n"
  putStrLn (show c2)
  putStrLn (show p2)


-- all further stuff is for "benchmarking"
-- set sizeBound=10 to get the same results as in the paper
conf1 :: Expr
conf1 = [expr|gEven(fSqr(x))|]
conf2 :: Expr
conf2 = [expr|fMatch(Cons(A(), Cons(A(), Nil())), s)|]

conf3 :: Expr
conf3 = [expr|fMatch(Cons(A(), Nil()), s)|]

-- input task
t1 = (conf1, prog1)
-- transformed task
t1t = transform t1
-- deforested task
t1d = deforest t1
-- supercompiled task
t1s = supercompile t1


run st n = sll_trace st [("x", peano n)]

def (e, p) = simplify $ foldTree $ buildFTree (driveMachine p) e
tr (e, p) = foldTree $ buildFTree (driveMachine p) e

t1d' = def t1
t1t' = tr t1

peano 0 = Ctr "Z" []
peano n = Ctr "S" [peano (n - 1)]


benchmark0 = map (snd . (run t1)) [0 .. 50]
benchmark1 = map (snd . (run t1t)) [0 .. 50]
benchmark2 = map (snd . (run t1d)) [0 .. 50]
benchmark3 = map (snd . (run t1s)) [0 .. 50]

points1 = zipWith3 (\n x1 x2 -> (n, (fromInteger x1) / (fromInteger x2))) [0 .. 50] benchmark0 benchmark1
points2 = zipWith3 (\n x1 x2 -> (n, (fromInteger x1) / (fromInteger x2))) [0 .. 50] benchmark0 benchmark2
points3 = zipWith3 (\n x1 x2 -> (n, (fromInteger x1) / (fromInteger x2))) [0 .. 50] benchmark0 benchmark3

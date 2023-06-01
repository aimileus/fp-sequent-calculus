\section{Sequent calculus}

There are many proof systems for all different sorts of logics. We have chosen
to implement generate proofs using a system called sequent calculus. A proof in
sequent calculus unsurprisingly consists of sequents: two finite multisets of
formulas \(\Gamma,\Delta\) written as \(\sequent{\Gamma}{\Delta}\). This can be
interpreted as a single formula by taking the conjunct of \(\Gamma\) and the
disjunct of \(\Delta\) and joining them using an implication:
\(\bigwedge\Gamma\to\bigvee\Delta\). We say a sequent is satisfiable if
this formula is.

We implement sequents in the following manner in Haskell together with a couple
of helper functions:

\begin{code}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}


module Sequent(
      Sequent(..),
      SimpleSequent(..),
      simpleMerge,
      simpleExp,
      seqSimple,
      leafs,
      greedyTree,
      verifyTree,
      allValidTrees,
      prove,
      Expandable(..),
      Expansion(..),
      SequentTree,
      Verifiable(..) )
   where

import Data.Maybe
import Data.List
import Test.QuickCheck (Arbitrary (arbitrary))
import Utils
import Latex

class Sequent s where
  ante :: s f -> [f]
  cons :: s f -> [f]
  fromAnte :: [f] -> s f
  fromCons :: [f] -> s f
  expand :: Expandable s f r => s f -> [Expanded s f r]

greedyTree :: (Sequent s, Expandable s f r) => s f -> SequentTree s f r
greedyTree zs = tree (expand zs)
    where
      tree [] = Axiom zs
      tree ((Expd children r):_) = Application r zs (greedyTree <$> children)

allValidTrees :: (Sequent s, Verifiable f, Expandable s f r) => s f -> [SequentTree s f r]
allValidTrees zs =  trees (expand zs)
  where
    -- trees :: [Expanded s f r] -> [SequentTree s f r]
    trees [] = [Axiom zs | verifyAxiom zs]
    trees exps = exps >>= expandSingle

    -- expandSingle :: Expanded s f r -> [SequentTree s f r]
    expandSingle (Expd ss r) = Application r zs <$> combs (allValidTrees <$> ss)

prove :: (Sequent s, Verifiable f, Expandable s f r) => s f -> Maybe (SequentTree s f r)
prove = listToMaybe . allValidTrees

applyExpansion :: s f -> Expansion s f r -> Maybe (Expanded s f r)
applyExpansion s (Exp m e r) = Just $ Expd (m s <$> e) r
applyExpansion _ (Atomic _) = Nothing

data SimpleSequent f = S [f] [f] deriving (Eq, Show)

instance Sequent SimpleSequent where
  ante (S a _) = a
  cons (S _ c) = c
  fromAnte xs = S xs []
  fromCons = S []

  expand s = mapMaybe (uncurry applyExpansion) (extractForm s)
    where
      extractForm :: (Expandable s f r) => SimpleSequent f -> [(SimpleSequent f, Expansion s f r)]
      extractForm (S l r) = lefts ++ rights
        where
          lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
          rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)



simpleMerge :: SimpleSequent p -> SimpleSequent p -> SimpleSequent p
simpleMerge (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

simpleExp :: [SimpleSequent f] -> r -> Expansion SimpleSequent f r
simpleExp = Exp simpleMerge
\end{code}

Our main concern in this project is proving sequents, which requires a notion of
provability. Just like any other proof system, there are axioms and rules to
create new things from axioms.

An axiom is simply just a single sequent which we assume to always be true. A
rule is a way to combine one or multiple sequents which have already been proven
to prove one single new sequent. This will be written as
\begin{mathpar}
    \inferrule{\sequent{\Gamma_{1}}{\Delta_{1}}\\\ldots\\\sequent{\Gamma_{n}}{\Delta_{n}}}{\sequent{\Gamma}{\Delta}}R.
\end{mathpar}
In practice, proofs in sequent calculus are often given as trees. Given a
sequent \(\sequent{\Gamma}{\Delta}\) that we want to prove we draw a tree of
sequents above it where each node of the tree represents an application of a
rule. Because a proof is inherently finite, all leafs of a correct proof must
be axioms.

This gives a very natural way to represent a sequent calculus proof in Haskell
as well: our proofs are trees where sequents are nodes and leafs are axioms.
\begin{code}
data SequentTree s f r
  = Axiom (s f)
  | Application r (s f) [SequentTree s f r]
  deriving (Eq, Show)

data Expansion s f r
  = Exp
      -- Make the Sequent type use in the merge function independent of f and r.
      -- Now it is slightly more convenient to convert sequents between formula
      -- types.
      { merge :: s f -> s f -> s f,
        exps :: [s f],
        rule :: r
      }
  | Atomic f

data Expanded s f r = Expd [s f] r

class Expandable s f r | f -> r where
  expandLeft :: f -> Expansion s f r
  expandRight :: f -> Expansion s f r

class Verifiable f where
  verifyAxiom :: Sequent s => s f -> Bool
  formSimple :: f -> Bool

seqSimple :: (Verifiable f) => SimpleSequent f -> Bool
seqSimple (S a c) = all formSimple a && all formSimple c

leafs :: SequentTree s f r -> [s f]
leafs (Axiom f) = return f
leafs (Application _ _ y) = y >>= leafs

verifyTree :: (Verifiable f) => SequentTree SimpleSequent f r -> Bool
verifyTree (Axiom f) = verifyAxiom f
verifyTree (Application _ _ ys) = all verifyTree ys

instance (Arbitrary f) => Arbitrary (SimpleSequent f) where
  arbitrary = S <$> arbitrary <*> arbitrary

instance (Arbitrary f, Expandable SimpleSequent f r) => Arbitrary (SequentTree SimpleSequent f r) where
  arbitrary = greedyTree . fromCons . return <$> arbitrary

\end{code}

\begin{code}
instance (ToLatex f) => ToLatex (SimpleSequent f) where
  toLatex :: SimpleSequent f -> String
  toLatex (S fs fs') = toCommaSeparated (toLatex <$> fs) ++ "\\Rightarrow " ++ toCommaSeparated (toLatex <$> fs')
    where
      toCommaSeparated :: [String] -> String
      toCommaSeparated = intercalate ","

instance (ToLatex f, ToLatex r, ToLatex (s f)) => ToLatex (SequentTree s f r) where
  toLatex (Axiom s) = "\\hypo{" ++ toLatex s ++ "}"
  toLatex (Application r s ss) = unlines $ (toLatex <$> ss) ++ ["\\infer" ++ show (length ss) ++ "[" ++ toLatex r ++ "]" ++ "{" ++ toLatex s ++ "}"]
\end{code}

\begin{code}
data Zipper a = Z [a] [a] deriving (Eq, Show)
data ZipperSequent f = ZS (Zipper f) (Zipper f) deriving (Eq, Show)

list2zipper :: [f] -> Zipper f
list2zipper xs = Z xs []

simple2zipper :: SimpleSequent f -> ZipperSequent f
simple2zipper (S xs ys) = ZS (list2zipper xs) (list2zipper ys)

zipper2list :: Zipper f -> [f]
zipper2list (Z xs ys) = xs ++ ys

zipper2simple :: ZipperSequent f -> SimpleSequent f
zipper2simple (ZS zx zy) = S (zipper2list zx) (zipper2list zy)

instance Sequent ZipperSequent where
  ante :: ZipperSequent f -> [f]
  ante = ante . zipper2simple
  cons :: ZipperSequent f -> [f]
  cons = cons . zipper2simple
  fromAnte :: [f] -> ZipperSequent f
  fromAnte = simple2zipper . fromAnte
  fromCons :: [f] -> ZipperSequent f
  fromCons = simple2zipper . fromCons

  -- TODO: extend the Expanded type with a None like type. Then the tree
  -- function could be generalized between implementations of Sequent
  expand (ZS (Z [] _) (Z [] _)) = []
  expand (ZS (Z (x:xs) y) z) = maybeToList $ ZS (Z xs y) z `applyExpansion` expandLeft x
  expand (ZS x (Z (y:ys) z)) = maybeToList $ ZS x (Z ys z) `applyExpansion` expandRight y

\end{code}

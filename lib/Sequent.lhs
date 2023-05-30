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

module Sequent(
      Sequent(..),
      SimpleSequent(..),
      simpleMerge,
      simpleExp,
      seqSimple,
      prove,
      leafs,
      verifyTree,
      Expandable(..),
      Expansion(..),
      SequentTree,
      Verfiable(..) )
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

data SimpleSequent f = S [f] [f] deriving (Eq, Show)

instance Sequent SimpleSequent where
  ante (S a _) = a
  cons (S _ c) = c
  fromAnte xs = S xs []
  fromCons = S []

simpleMerge :: SimpleSequent p -> SimpleSequent p -> SimpleSequent p
simpleMerge (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

simpleExp :: [SimpleSequent f] -> r -> Expansion f r
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
data SequentTree f r
  = Axiom (SimpleSequent f)
  | Application r (SimpleSequent f) [SequentTree f r]
  deriving (Eq, Show)

data Expansion f r
  = Exp
      -- Make the Sequent type use in the merge function independent of f and r.
      -- Now it is slightly more convenient to convert sequents between formula
      -- types.
      { merge :: forall a. SimpleSequent a -> SimpleSequent a -> SimpleSequent a,
        exps :: [SimpleSequent f],
        rule :: r
      }
  | AtomicL f
  | AtomicR f

data Expanded f r = Expd [SimpleSequent f] r

class Expandable f r | f -> r where
  expandLeft :: f -> Expansion f r
  expandRight :: f -> Expansion f r

class Verfiable f where
  verifyAxiom :: SimpleSequent f -> Bool
  formSimple :: f -> Bool

seqSimple :: (Verfiable f) => SimpleSequent f -> Bool
seqSimple (S a c) = all formSimple a && all formSimple c

applyExpansion :: SimpleSequent f -> Expansion f r -> Maybe (Expanded f r)
applyExpansion s (Exp m e r) = Just $ Expd (m s <$> e) r
applyExpansion _ (AtomicL _) = Nothing
applyExpansion _ (AtomicR _) = Nothing

-- TODO: use zipper lists here instead of this mildly computationally intensive way.
extractForm :: (Expandable f r) => SimpleSequent f -> [(SimpleSequent f, Expansion f r)]
extractForm (S l r) = lefts ++ rights
  where
    lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
    rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)

prove :: (Expandable f r) => SimpleSequent f -> SequentTree f r
prove s = tree expanded
  where
    expanded = listToMaybe $ mapMaybe (uncurry applyExpansion) (extractForm s)

    tree Nothing = Axiom s
    tree (Just (Expd e r)) = Application r s (prove <$> e)

leafs :: SequentTree f r -> [SimpleSequent f]
leafs (Axiom f) = return f
leafs (Application _ _ y) = y >>= leafs

verifyTree :: (Verfiable f) => SequentTree f r -> Bool
verifyTree (Axiom f) = verifyAxiom f
verifyTree (Application _ _ ys) = all verifyTree ys

instance (Arbitrary f) => Arbitrary (SimpleSequent f) where
  arbitrary = S <$> arbitrary <*> arbitrary

instance (Arbitrary f, Expandable f r) => Arbitrary (SequentTree f r) where
  arbitrary = prove . fromCons . return <$> arbitrary

\end{code}

\begin{code}
instance (ToLatex f) => ToLatex (SimpleSequent f) where
  toLatex :: SimpleSequent f -> String
  toLatex (S fs fs') = toCommaSeparated (toLatex <$> fs) ++ "\\Rightarrow " ++ toCommaSeparated (toLatex <$> fs')
    where
      toCommaSeparated :: [String] -> String
      toCommaSeparated = intercalate ","

instance (ToLatex f, ToLatex r) => ToLatex (SequentTree f r) where
  toLatex (Axiom s) = "\\hypo{" ++ toLatex s ++ "}"
  toLatex (Application r s ss) = unlines $ (toLatex <$> ss) ++ ["\\infer" ++ show (length ss) ++ "[" ++ toLatex r ++ "]" ++ "{" ++ toLatex s ++ "}"]
\end{code}

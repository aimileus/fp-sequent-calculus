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

module Sequent where

import Data.Maybe
import Test.QuickCheck (Arbitrary (arbitrary))
import Utils

data Sequent f = S
  { ante :: [f],
    cons :: [f]
  }
  deriving (Eq, Show)

simpleMerge :: Sequent p -> Sequent p -> Sequent p
simpleMerge (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

simpleExp :: [Sequent f] -> r -> Expansion f r
simpleExp = Exp simpleMerge

fromAnte :: [f] -> Sequent f
fromAnte fs = S fs []

fromCons :: [f] -> Sequent f
fromCons = S []
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
  = Axiom (Sequent f)
  | Application r (Sequent f) [SequentTree f r]
  deriving (Eq, Show)

data Expansion f r
  = Exp
      -- Make the Sequent type use in the merge function independent of f and r.
      -- Now it is slightly more convenient to convert sequents between formula
      -- types.
      { merge :: forall a. Sequent a -> Sequent a -> Sequent a,
        exps :: [Sequent f],
        rule :: r
      }
  | AtomicL f
  | AtomicR f

data Expanded f r = Expd
  { expds :: [Sequent f],
    rule' :: r
  }

class Expandable f r | f -> r where
  expandLeft :: f -> Expansion f r
  expandRight :: f -> Expansion f r

class Verfiable f where
  verifyAxiom :: Sequent f -> Bool
  formSimple :: f -> Bool

seqSimple :: (Verfiable f) => Sequent f -> Bool
seqSimple (S a c) = all formSimple a && all formSimple c

applyExpansion :: Sequent f -> Expansion f r -> Maybe (Expanded f r)
applyExpansion s (Exp m e r) = Just $ Expd (m s <$> e) r
applyExpansion _ (AtomicL _) = Nothing
applyExpansion _ (AtomicR _) = Nothing

-- TODO: use zipper lists here instead of this mildly computationally intensive way.
extractForm :: (Expandable f r) => Sequent f -> [(Sequent f, Expansion f r)]
extractForm (S l r) = lefts ++ rights
  where
    lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
    rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)

prove :: (Expandable f r) => Sequent f -> SequentTree f r
prove s = tree expanded
  where
    expanded = listToMaybe $ mapMaybe (uncurry applyExpansion) (extractForm s)

    tree Nothing = Axiom s
    tree (Just (Expd e r)) = Application r s (prove <$> e)

leafs :: SequentTree f r -> [Sequent f]
leafs (Axiom f) = return f
leafs (Application _ _ y) = y >>= leafs

verifyTree :: (Verfiable f) => SequentTree f r -> Bool
verifyTree (Axiom f) = verifyAxiom f
verifyTree (Application _ _ ys) = all verifyTree ys

instance (Arbitrary f) => Arbitrary (Sequent f) where
  arbitrary = S <$> arbitrary <*> arbitrary

instance (Arbitrary f, Expandable f r) => Arbitrary (SequentTree f r) where
  arbitrary = prove . fromCons . return <$> arbitrary

\end{code}
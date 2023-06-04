\ignore{
\begin{code}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}

module Sequent
  ( Sequent (..),
    SimpleSequent (..),
    simpleMerge,
    simpleExp,
    seqSimple,
    leafs,
    greedyTree,
    verifyTree,
    allValidTrees,
    prove,
    simple2zipper,
    zipper2simple,
    Expandable (..),
    Expansion (..),
    SequentTree(..),
    Verifiable (..),
  )
where
import Data.List
import Data.Maybe
import Latex
import Test.QuickCheck (Arbitrary (arbitrary))
import Utils
\end{code}
}

\section{Sequent calculus}

There are many proof systems for all different sorts of logics. We have chosen
to implement generate proofs using a system called sequent calculus. A proof in
sequent calculus unsurprisingly consists of sequents: two finite multisets of
formulas \(\Gamma,\Delta\) written as \(\sequent{\Gamma}{\Delta}\). This can be
interpreted as a single formula by taking the conjunct of \(\Gamma\) and the
disjunct of \(\Delta\) and joining them using an implication:
\(\bigwedge\Gamma\to\bigvee\Delta\). We say a sequent is satisfiable if
this formula is.

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
Note that our typeclass includes a function called expand, we will explain this
later when explaining our approach to generating proofs.
\begin{code}
class Sequent s where
  ante :: s f -> [f]
  cons :: s f -> [f]
  fromAnte :: [f] -> s f
  fromCons :: [f] -> s f
  expand :: Expandable s f r => s f -> [Expanded s f r]

data SequentTree s f r
  = Axiom (s f)
  | Application r (s f) [SequentTree s f r]
  deriving (Eq, Show)

class Verifiable f where
  verifyAxiom :: (Sequent s) => s f -> Bool
  formSimple :: f -> Bool

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

seqSimple :: (Verifiable f) => SimpleSequent f -> Bool
seqSimple (S a c) = all formSimple a && all formSimple c

\end{code}
We use a typeclass for anything that looks like a sequent, which will allow us
to create different kinds of sequents. We will show an example of this later.

We implement the following functions to verify whether a given proof in sequent
calculus has valid axioms as leaves. We assume that any proof we generate will
have correct steps in between, so when the leaves of a proof are indeed axioms
the proof will be valid.
\begin{code}
leafs :: SequentTree s f r -> [s f]
leafs (Axiom f) = return f
leafs (Application _ _ y) = y >>= leafs

verifyTree :: (Verifiable f) => SequentTree SimpleSequent f r -> Bool
verifyTree (Axiom f) = verifyAxiom f
verifyTree (Application _ _ ys) = all verifyTree ys

\end{code}

\subsection{Generating proofs}
We generate proofs essentially using a depth first search. Given some target
sequent \(\sequent{\Gamma}{\Delta}\), we compute all possible rule applications
that could lead to that sequent. If there is some rule \(R\) such that
\begin{mathpar}
    \inferrule{\sequent{\Gamma_{1}}{\Delta_{1}}\\\ldots\\\sequent{\Gamma_{n}}{\Delta_{n}}}{\sequent{\Gamma}{\Delta}}R
\end{mathpar}
is a valid inference, we encode the sequents
\(\sequent{\Gamma_{1}}{\Delta_{1}},\ldots,\sequent{\Gamma_{n}}{\Delta_{n}}\)
using something we call Expansions. In most cases the original sequent
\(\sequent{\Gamma}{\Delta}\) is very similar to the sequents
\(\sequent{\Gamma_{i}}{\Delta_{i}}\). Therefore we encode the changes to a
sequent by keeping track of the changes to a sequent and use a function to
specify how we want to apply these changes. We also note the specific rule
used to obtain this particular expansion. Some formulas cannot be expanded upon,
we call such formulas atomic.

In order to actually construct a tree from such an expansion, we have a function
which will apply the changes specified in the expansion to a base sequent
to get a new list of sequents. We can recursively compute such expansions
to get a possibly valid proof.

\begin{code}
data Expansion s f r
  = Exp (s f -> s f -> s f) [s f] r
  | Atomic f

data Expanded s f r = Expd [s f] r

applyExpansion :: s f -> Expansion s f r -> Maybe (Expanded s f r)
applyExpansion s (Exp m e r) = Just $ Expd (m s <$> e) r
applyExpansion _ (Atomic _) = Nothing
\end{code}

In most systems of sequent calculus a rule application only adds a single
formula to the consequent or antecedent of a sequent. This formula is then
called the principal formula. Therefore in practice we build all expansions
by computing the expansion if some formula was principal. This means we can
compute expansions from a single formula which occurs somewhere in a sequent.
This is what the Expandable typeclass represents.

\begin{code}
class Expandable s f r | f -> r where
  expandLeft :: f -> Expansion s f r
  expandRight :: f -> Expansion s f r

simpleMerge :: SimpleSequent p -> SimpleSequent p -> SimpleSequent p
simpleMerge (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

simpleExp :: [SimpleSequent f] -> r -> Expansion SimpleSequent f r
simpleExp = Exp simpleMerge
\end{code}
Now our proof generation is simply a matter of combining all pieces. We have two
methods of proof generation: the first is greedy, and the second is using a
depth first approach.

The greedy approach is very simple: it will simply pick the first possible
expansion and apply it. This will obviously not work for more complex logics,
bit one can prove that it works for propositional logic.

For more complex logics, we perform a depth first search. This works for most
logics because it turns out that rule applications create more complex sequents.
This is easily seen in \Cref{fig:seq-rules}, where rules create formulas of
higher complexity from smaller ones. This means that one can only apply finitely
many rules before reaching an atomic formula and therefore there are finitely
many possible (possibly invalid) proof trees. We lazily iterate these using a
depth first search and verify whether the leaves are axioms to see if it is a
valid proof.
\begin{code}
greedyTree :: (Sequent s, Expandable s f r) => s f -> SequentTree s f r
greedyTree zs = tree (expand zs)
  where
    tree [] = Axiom zs
    tree ((Expd children r) : _) = Application r zs (greedyTree <$> children)

allValidTrees :: forall s f r. (Sequent s, Verifiable f, Expandable s f r) => s f -> [SequentTree s f r]
allValidTrees zs = trees (expand zs)
  where
    -- trees :: [Expanded s f r] -> [SequentTree s f r]
    trees [] = [Axiom zs | verifyAxiom zs]
    trees exps = exps >>= expandSingle

    -- expandSingle :: Expanded s f r -> [SequentTree s f r]
    expandSingle (Expd ss r) = Application r zs <$> combs (allValidTrees <$> ss)

prove :: (Sequent s, Verifiable f, Expandable s f r) => s f -> Maybe (SequentTree s f r)
prove = listToMaybe . allValidTrees
\end{code}

In order to test properly, we implement generating sequents for any formula type
which implements being randomly generated.

\begin{code}
instance (Arbitrary f) => Arbitrary (SimpleSequent f) where
  arbitrary = fromCons . return <$> arbitrary

instance (Arbitrary f, Expandable SimpleSequent f r) => Arbitrary (SequentTree SimpleSequent f r) where
  arbitrary = greedyTree . fromCons . return <$> arbitrary

instance (ToLatex f) => ToLatex (SimpleSequent f) where
  toLatex :: SimpleSequent f -> String
  toLatex (S fs fs') = toCommaSeparated (toLatex <$> fs) ++ "\\Rightarrow " ++ toCommaSeparated (toLatex <$> fs')
    where
      toCommaSeparated :: [String] -> String
      toCommaSeparated = intercalate ","

instance (ToLatex f, ToLatex r, ToLatex (s f)) => ToLatex (SequentTree s f r) where
  toLatex tree = "\\begin{prooftree}\n" ++ helper tree ++ "\n\\end{prooftree}"
    where
      helper (Axiom s) = "\\hypo{" ++ toLatex s ++ "}"
      helper (Application r s ss) = unlines $ (helper <$> ss) ++ ["\\infer" ++ show (length ss) ++ "[\\(" ++ toLatex r ++ "\\)]" ++ "{" ++ toLatex s ++ "}"]
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

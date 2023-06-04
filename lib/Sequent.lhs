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
    leafs,
    greedyTree,
    verifyTree,
    allValidTrees,
    prove,
    applyExpansion,
    Expandable (..),
    Expansion (..),
    SequentTree,
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
as well: our proofs are trees where sequents are nodes and leafs are axioms. Most of
our code is independent of the specific data structure used to store the sequent in
Haskell. We use a typeclass for anything that looks like a sequent, which will allow
us to create different kinds of sequents. We will show an example of this later.
In instance of Sequent  stores formula of type \texttt{f}. Here \texttt{f} depends
on the specific logic stored in the sequent. Note that our typeclass includes a
function called expand, we will explain this later when explaining our approach to generating proofs.
\begin{code}
class Functor s => Sequent s where
  ante :: s f -> [f]
  cons :: s f -> [f]
  fromAnte :: [f] -> s f
  fromCons :: [f] -> s f
  expand :: Expandable s f r => s f -> [Expanded s f r]
\end{code}
To store the tree we implement a simple tree-like recursive data structure.
For the non-leaf nodes, we store the inference rule of type \texttt{r} used.
\begin{code}
data SequentTree s f r
  = Axiom (s f)
  | Application r (s f) [SequentTree s f r]
  deriving (Eq, Show)
\end{code}

When we implement sequents storing formula of type \texttt{f}. We need to be
able to check, whether the proof tree is done, and the current node is an axiom.
\begin{code}
class Verifiable f where
  verifyAxiom :: (Sequent s) => s f -> Bool
\end{code}

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

The most simple data structure Sequent stores both the consequents and the antecedents
in a simple list.
\begin{code}
data SimpleSequent f = S [f] [f] deriving (Eq, Show)

instance Sequent SimpleSequent where
  ante (S a _) = a
  cons (S _ c) = c
  fromAnte xs = S xs []
  fromCons = S []
  expand = expandSimple
\end{code}
We will give \texttt{expandSimple} function later, when
we have explained how the expand function works.

To slightly make our live easier in some later functions, we make SimpleSequent
a Functor instance.

\begin{code}
instance Functor SimpleSequent where
  fmap f (S a c) = S (f <$> a) (f <$> c)
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
using something we call an \texttt{Expansion}. In most cases the original sequent
\(\sequent{\Gamma}{\Delta}\) is very similar to the sequents
\(\sequent{\Gamma_{i}}{\Delta_{i}}\).

An \texttt{Expansion} is a polymorphic Haskell data type which is dependent on
the logic, and the data structure of the sequent. The parameters of
\texttt{Expansion} are
\begin{itemize}
  \item \texttt{f}: The Haskell type for the formulae of the logic used in the sequent.
  \item \texttt{s}: A specific \texttt{Sequent} instance.
  \item \texttt{r}: A Haskell type used to store the inference rule used in the \texttt{Expansion}.
\end{itemize}

An \texttt{Expansion} is generated from some sequent \(\sequent{\Phi}{\Psi}\),
where \(\Phi \subseteq \Gamma\), and \(\Psi \subseteq \Delta\). The \texttt{Expansion}
then tells us how to \(\sequent{\Phi}{\Psi}\) are modified, and how to merge the other formula
in every \(\sequent{\Gamma_i}{\Delta_i}\).

The \texttt{Expansion} stores a list of type \texttt{[s f]}, which stores sequents
of the form \(\sequent{\Phi_i}{\Psi_i}\). Every \(\sequent{\Phi_i}{\Psi_i}\) represents
how \(\sequent{\Phi_i}{\Psi_i}\) is modified in \(\sequent{\Gamma_{i}}{\Delta_{i}}\).
Let \(\Gamma' =\Gamma \setminus \Phi\) and \(\Delta' = \Delta \setminus \Psi\).
The \texttt{Expansion} also gives a function that can merge \(\sequent{\Phi_i}{\Psi_i}\)
with \(\sequent{\Gamma'}{\Delta'}\) into \(\sequent{\Gamma_i}{\Delta_i}\).
We also note the specific rule used to obtain this particular expansion using
the type \texttt{r}. Some formulas cannot be expanded upon, we call such formulas atomic.

\begin{code}
data Expansion s f r
  = Exp (s f -> s f -> s f) [s f] r
  | Atomic f
\end{code}

Note that an expansion is independent from \(\sequent{\Gamma'}{\Delta'}\).
In order to actually construct a tree from such an
expansion, we have a function which will apply the changes specified in the
expansion to the base sequent \(\sequent{\Gamma'}{\Delta'}\) to get a new list of sequents.
We can recursively compute such expansions to get a possibly valid proof.

\begin{code}
data Expanded s f r = Expd [s f] r

applyExpansion :: s f -> Expansion s f r -> Maybe (Expanded s f r)
applyExpansion s (Exp m e r) = Just $ Expd (m s <$> e) r
applyExpansion _ (Atomic _) = Nothing
\end{code}

In most systems of sequent calculus a rule application only adds a single
formula to the consequent or antecedent of a sequent. Therefore \(\sequent{\Phi}{\Psi}\)
is of the form \(\sequent{\phi}{}\) or \(\sequent{}{\psi}\), for some formula \(\phi\)
and \(\psi\). This formula \(\phi\) or \(\psi\) is then called the principal formula.
Therefore in practice we build all expansions by computing the expansion if some
formula was principal. This means we can compute expansions from a single formula
which occurs somewhere in either the antecedents or the consequents.
This is what the Expandable typeclass represents.

\begin{code}
class (Sequent s, Verifiable f) => Expandable s f r | f -> r where
  expandLeft :: f -> Expansion s f r
  expandRight :: f -> Expansion s f r
\end{code}

For a \texttt{SimpleSequent} we can try to expand all formulae in both the antecedent
and the consequent. We use here that Haskell is lazy, so when we only need a single
instance of \texttt{Expanded}, it is not necessary to compute the entire list. On
the other hand, this operation may still be expensive when all

\begin{code}
expandSimple :: Expandable SimpleSequent f r => SimpleSequent f -> [Expanded SimpleSequent f r]
expandSimple s = mapMaybe (uncurry applyExpansion) (extractForm s)
    where
      extractForm (S l r) = lefts ++ rights
        where
          lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
          rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)
\end{code}

In most cases, the merging of the sequents \(\sequent{\Phi_i}{\Psi_i}\) with
\(\sequent{\Gamma'}{\Delta'}\) is simply the \(\sequent{\Phi_i \cup \Gamma'}{\Psi_i \cup \Delta'}\).
Therefore we define these helper functions for the common case.
\begin{code}
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
but one can prove that it works for classical propositional logic.

\begin{code}
greedyTree :: (Sequent s, Expandable s f r) => s f -> SequentTree s f r
greedyTree zs = if verifyAxiom zs then Axiom zs else tree (expand zs)
  where
    tree [] = Axiom zs
    tree ((Expd children r) : _) = Application r zs (greedyTree <$> children)
\end{code}

For more complex logics, we perform a depth first search that generate all possible
trees that generate the target sequent. This works for most
logics because it turns out that rule applications create more complex sequents.
This is easily seen in \Cref{fig:seq-rules}, where rules create formulas of
higher complexity from smaller ones. This means that one can only apply finitely
many rules before reaching an atomic formula and therefore there are finitely
many possible (possibly invalid) proof trees. We lazily iterate these using a
depth first search and verify whether the leaves are axioms to see if it is a
valid proof.

\begin{code}
allValidTrees :: Expandable s f r => s f -> [SequentTree s f r]
allValidTrees zs = trees (expand zs)
  where
    trees [] = [Axiom zs | verifyAxiom zs]
    trees e = e >>= expandSingle

    expandSingle (Expd ss r) = Application r zs <$> combs (allValidTrees <$> ss)

prove :: Expandable s f r => s f -> Maybe (SequentTree s f r)
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

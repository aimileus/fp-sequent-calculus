\ignore{
\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ModalSeq where

import PropSeq
import Sequent
import Data.List
import Latex
\end{code}}
\section{Modal Logic}
We can also use our Sequent Calculus prover for modal logic formula. Modal logic
extends propositional logic with two modal operators \(\Box\), and \(\Diamond\).
A modal formula \(\phi\) is of the form
\[
  \varphi = \psi \mid \Box \varphi \mid \Diamond \varphi
\]
where \(\psi\) is an arbitrary propositional formula.

\begin{code}
data ModalForm p = Dia (ModalForm p) | Box (ModalForm p) | Prop (PropForm p) deriving (Eq, Show)

type MSequent p = SimpleSequent (ModalForm p)
\end{code}
We restrict ourselfs to S4 models of modal logic, which mean that world relation
is reflexive and transitive. The inference rules of modal logic are based on the
propositional inference rules. Here we use classical propositional logic.
The extended inference rules are as follows

\begin{mathpar}
  \inferrule{\sequent{\Gamma, \varphi}{\Delta}}{\sequent{\Gamma, \Box \varphi}{\Delta}}\Box L
  \and   \inferrule{\sequent{\Gamma^*}{\Delta^*, \varphi}}{\sequent{\Gamma}{\Delta, \Box \varphi}}\Box R \\

   \inferrule{\sequent{\Gamma^*, \varphi}{\Delta^*}}{\sequent{\Gamma, \Diamond \varphi}{\Delta}}\Diamond L
  \and    \inferrule{\sequent{\Gamma}{\Delta, \varphi}}{\sequent{\Gamma}{\Delta, \Diamond \varphi}}\Diamond R
\end{mathpar}
where \(\Gamma\) and \(\Delta\) are the following filtered subsets \begin{align*}
  \Gamma^* & := \{\Box \varphi \mid \Box \varphi \in \Gamma\} \\
  \Delta^* & := \{\Diamond \varphi \mid \Diamond \varphi \in \Delta\}
\end{align*}
We can represent a modal rule as an extension of \texttt{PropRule}
\begin{code}
data ModalRule = DiaL | DiaR | BoxL | BoxR | PropR PropRule deriving (Eq, Show)
\end{code}

The definition of an axiom is unchanged for modal logic.

\begin{code}
instance (Eq p) => Verifiable (ModalForm p) where
  verifyAxiom :: Sequent s => s (ModalForm p) -> Bool
  verifyAxiom s = (Prop Bot `elem` a) || (Prop Top `elem` c) || (not . null) (a `intersect` c)
    where
      a = ante s
      c = cons s
\end{code}

Like with the intuitionistic logic, we want to reuse our definitions from
classical propositional logic as much as possible. Therefore, we define some a
function to convert classical propositional expansions to modal expansions.

It is difficult to convert a merge function on \texttt{PropForm}, to a merge
function on \texttt{ModalForm}. Here we abuse the fact that we know for
classical logic, the merge function \texttt{\_m} will be \texttt{simpleMerge}.
\begin{code}
modSeq :: Sequent s => s (PropForm p) -> s (ModalForm p)
modSeq = (Prop <$>)

expPropToModal :: Expansion SimpleSequent (PropForm p) PropRule -> Expansion SimpleSequent (ModalForm p) ModalRule
expPropToModal (Exp _m e r) = simpleExp (modSeq <$> e) (PropR r)
expPropToModal (Atomic f) = Atomic (Prop f)
\end{code}
Then we can implement the \texttt{mergeMod} function to convert \(\Gamma\) and
\(\Delta\) to \(\Gamma^*\) and \(\Delta^*\).
\begin{code}
mergeMod :: MSequent p -> MSequent p -> MSequent p
mergeMod (S a1 c1) (S a2 c2) = S (filter isBox a1 ++ a2) (filter isDia c1 ++ c2) where
  isBox (Box _) = True
  isBox _ = False

  isDia (Dia _) = True
  isDia _ = False
\end{code}

With the prerequisites, it is then fairly easy to define the expansions for
modal logic.
\begin{code}
instance (Eq p) => Expandable SimpleSequent (ModalForm p) ModalRule where
  expandLeft :: ModalForm p -> Expansion SimpleSequent (ModalForm p) ModalRule
  expandLeft (Dia f) = Exp mergeMod [S [f] []] DiaL
  expandLeft (Box f) = Exp simpleMerge [S [f] []] BoxL
  expandLeft (Prop f) = expPropToModal $ expandLeft f

  expandRight :: ModalForm p -> Expansion SimpleSequent (ModalForm p) ModalRule
  expandRight (Dia f) = Exp simpleMerge [S [] [f]] DiaR
  expandRight (Box f) = Exp mergeMod [S [] [f]] BoxR
  expandRight (Prop f) = expPropToModal $ expandRight f
\end{code}
Again it is easy to see that as with the intuitionistic classical logic, a greedy
search is not always sufficient to find a proof. Therefore it is necessary to use
a more thorough search algorithm, such as \texttt{allValidTrees}.

\begin{code}
instance ToLatex p => ToLatex (ModalForm p) where
  toLatex (Prop f) = toLatex f
  toLatex (Box f) = "\\Box (" ++ toLatex f ++ ")"
  toLatex (Dia f) = "\\Diamond (" ++ toLatex f ++ ")"

instance ToLatex ModalRule where
  toLatex BoxL = "\\Box L"
  toLatex BoxR = "\\Box R"
  toLatex DiaL = "\\Diamond L"
  toLatex DiaR = "\\Diamond R"
  toLatex (PropR f) = toLatex f
\end{code}

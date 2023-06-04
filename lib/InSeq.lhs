\ignore{
\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module InSeq where

import Latex (ToLatex (..))
import PropSeq (PropForm (..), PropRule)
import Sequent
import Data.List
import Test.QuickCheck (Arbitrary, arbitrary)
\end{code}
}

\subsection{Intuitionistic logic}
With all of the work we have done so far, implementing intuitionistic logic is
rather easy. We can even reuse the type of propositional formulas from before.

The axioms of intuitionistic sequent calculus are the same as for
propositional logic. In fact, only a single rule is different between the two:
the right implication rule is given by
\[
    \inferrule{\sequent{\Gamma,\varphi}{\psi}}{\sequent{\Gamma}{\varphi\to\psi,\Delta}}\to R
\]
where \(\Delta\) is any arbitrary multiset. \cite{syllabus} We implement expansion of
\(\neg\varphi\) using the rules for implication as well by simply handling
\(\neg\varphi\) as if it were the formula \(\varphi\to\bot\).

The new inference rule does have a significant difference from the classical
inference rules, namely the Expansion using this rule might be ``destructive''.
By applying the wrong inference rule, it can be possible to go from a provable
sequent to an unprovable sequent. Take for this invalid proof
\[
\begin{prooftree}
\hypo{p_{1}\Rightarrow \bot }
\infer1[\(\to R\)]{p_{1}\Rightarrow p_{1}\to (\bot ),p_{1}\to (\top )}
\end{prooftree}
\]
where the correct proof would be
\[
\begin{prooftree}
\hypo{p_{1}\Rightarrow \top }
\infer1[\(\to R\)]{p_{1}\Rightarrow p_{1}\to \bot ,p_{1}\to \top }
\end{prooftree}
\]
We define an intuitionistic formula as a newtype over the classical propositional formula.
Therefore, the compiler knows whether a formula is classical or intuitionistic,
and can call the appropriate functions to generate the proof. On the other hand
there is no runtime overhead, and the in-memory representation of intuitionistic
formula is the same as for classical formula.
\begin{code}
newtype InForm p = In (PropForm p)
  deriving (Eq, Show)

data InRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

type ISequent p = SimpleSequent (InForm p)
\end{code}
First we introduce some functions to easily convert between classical and
intuitionistic formula/sequents/expansions
\begin{code}
clas :: InForm f -> PropForm f
clas (In f) = f

clasSeq :: Sequent s => s (InForm f) -> s (PropForm f)
clasSeq = (clas <$>)

inSeq :: Sequent s => s (PropForm f) -> s (InForm f)
inSeq = (In <$>)
\end{code}

The axioms for intuitionistic formula are the same as for classical formula.

\begin{code}
instance (Eq p) => Verifiable (InForm p) where
  verifyAxiom :: Sequent s => s (InForm p) -> Bool
  verifyAxiom = verifyAxiom . clasSeq
\end{code}

We see that it is very convenient to declare intuisiontistic functions in terms
of their classical functions. Therefore, we define more functions to convert between
intuitionistic and classical data structures.

\begin{code}
clasRule :: InRule -> PropRule
clasRule = toEnum . fromEnum

inRule :: PropRule -> InRule
inRule = toEnum . fromEnum

inExpandable :: Sequent s => Expansion s (PropForm p) PropRule -> Expansion s (InForm p) InRule
inExpandable (Exp m s r) = Exp (inMerge m) (inSeq <$> s) (inRule r)
  where
    inMerge m1 s1 s2 = inSeq $ m1 (clasSeq s1) (clasSeq s2)
inExpandable (Atomic f) = Atomic (In f)
\end{code}

Now we can easily define the expansions for intuitionistic logic. Here we can
reuse the classical expansions

\begin{code}
instance Eq p => Expandable SimpleSequent (InForm p) InRule where
  expandLeft :: Eq p => InForm p -> Expansion SimpleSequent (InForm p) InRule
  expandLeft (In (Neg phi)) = simpleExp [fromAnte [In (phi `Impl` Bot)]] NegL
  expandLeft (In f) = inExpandable (expandLeft f)

  expandRight :: Eq p => InForm p -> Expansion SimpleSequent (InForm p) InRule
  expandRight (In (Neg phi)) = simpleExp [fromCons [In (phi `Impl` Bot)]] NegR
  expandRight (In (phi `Impl` psi)) = Exp mergeRightImpl [S [In phi] [In psi]] ImplR
    where
      mergeRightImpl (S a1 _c1) (S a2 c2) = S (nub (a1 ++ a2)) c2
  expandRight (In f) = inExpandable (expandRight f)
\end{code}

Finally we also make intuitionistic formulae instances of ToLatex and Arbitrary.

\begin{code}
instance ToLatex InRule where
  toLatex = toLatex . clasRule

instance ToLatex p => ToLatex (InForm p) where
  toLatex = toLatex . clas

instance (Arbitrary p) => Arbitrary (InForm p) where
  arbitrary = In <$> arbitrary
\end{code}

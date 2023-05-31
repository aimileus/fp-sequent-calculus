\subsection{Propositional logic}

The language of propositional logic should be familiar to everyone. It can be
expressed in a Context Free Grammar as such:
\[
    \varphi=P\mid\varphi\vee\varphi\mid\varphi\wedge\varphi\mid\varphi\to\varphi\mid\neg\varphi
\]
where \(P\) is any set of propositional letters. In Haskell we implement it as a
data type generic over a type \(p\) which is the type of the propositional
letters.

We also have a simple function to determine if a formula is a propositional
letter.

\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PropSeq where

import Data.List
import Sequent
    ( fromAnte,
      fromCons,
      simpleExp,
      Expandable(..),
      Expansion(..),
      SimpleSequent(S),
      SequentTree,
      Verfiable(..) )
import Test.QuickCheck (Arbitrary (arbitrary), oneof, sized)
import Latex

type Prop = Int

data PropForm p
  = P p
  | Neg (PropForm p)
  | Conj (PropForm p) (PropForm p)
  | Disj (PropForm p) (PropForm p)
  | Impl (PropForm p) (PropForm p)
  | Bot
  | Top
  deriving (Eq, Show)

(-->) :: PropForm p -> PropForm p -> PropForm p
(-->) = Impl
infixr 4 -->

(&) :: PropForm p -> PropForm p -> PropForm p
(&) = Conj
infixr 5 &
\end{code}

\subsubsection{Propositional sequent calculus}
The following are the axioms of propositional sequent calculus:
\[
    \sequent{\bot,\Gamma}{\Delta}\qquad\sequent{\Gamma}{\Delta,\top}\qquad\sequent{\Gamma,\varphi}{\varphi,\Delta}
\]
The inference rules are given in \Cref{fig:seq-rules}.
\begin{figure}[H]
    \begin{mathpar}
        \inferrule{\sequent{\Gamma,\varphi,\psi}{\Delta}}{\sequent{\Gamma,\varphi\wedge\psi}{\Delta}}\wedge L
        \and \inferrule{\sequent{\Gamma}{\Delta,\varphi}\\\sequent{\Gamma}{\Delta,\psi}}{\sequent{\Gamma}{\Delta,\varphi\wedge\psi}}\wedge R\\

        \inferrule{\sequent{\Gamma,\varphi}{\Delta}\\\sequent{\Gamma,\psi}{\Delta}}{\sequent{\Gamma,\varphi\vee\psi}{\Delta}}\vee L
        \and\inferrule{\sequent{\Gamma}{\Delta,\varphi,\psi}}{\sequent{\Gamma}{\Delta,\varphi\vee\psi}}\vee R \\

        \inferrule{\sequent{\Gamma}{\Delta,\varphi}}{\sequent{\Gamma,\neg\varphi}{\Delta}}\neg L
        \and\inferrule{\sequent{\Gamma,\varphi}{\Delta}}{\sequent{\Gamma}{\Delta,\neg\varphi}}\neg R \\

        \inferrule{\sequent{\Gamma,\varphi}{\Delta}\\\sequent{\Gamma}{\Delta,\varphi}}{\sequent{\Gamma,\varphi\to\psi}{\Delta}}\to L
        \and\inferrule{\sequent{\Gamma,\varphi}{\Delta,\psi}}{\sequent{\Gamma}{\Delta,\varphi\to\psi}}\to R
    \end{mathpar}

    \caption{The rules for sequent calculus.}
    \label{fig:seq-rules}
\end{figure}

We give a couple of examples of proofs of sequents:

\begin{figure}[ht]
    \centering
    \begin{prooftree}
        \hypo{\sequent{p}{p,q}}
        \infer1[\(\neg L\)]{\sequent{p,\neg p}{q}}
        \infer1[\(\to R\)]{\sequent{p}{\neg p\to q}}
    \end{prooftree}

    \caption{A proof of the sequent \(\sequent{p}{\neg p\to q}\)}
\end{figure}

\begin{figure}[ht]
    \centering
    \begin{prooftree}
        \hypo{\sequent{q}{p,q}}

        \hypo{\sequent{p}{p,q}}
        \infer1[\(\neg L\)]{\sequent{}{\neg p,p,q}}
        \infer2[\(\to L\)]{\sequent{\neg p\to q}{p,q}}

        \hypo{\sequent{q,\neg p\to q}{q}}

        \infer2[\(\to L\)]{\sequent{p\to q,\neg p\to q}{q}}
        \infer1[\(\to R\)]{\sequent{p\to q}{(\neg p\to q)\to q}}
        \infer1[\(\to R\)]{\sequent{}{(p\to q)\to((\neg p\to q)\to q)}}
    \end{prooftree}

    \caption{A proof of the tautology \((p\to q)\to((\neg p\to q)\to q)\)}
\end{figure}

We implement the types from the sequent module in order to use its functions to
create proofs:
\begin{code}
type PSequent p = SimpleSequent (PropForm p)

type PSeqTree p = SequentTree SimpleSequent (PropForm p) PropRule

data PropRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

instance Expandable SimpleSequent (PropForm p) PropRule where
  expandLeft :: PropForm p -> Expansion SimpleSequent (PropForm p) PropRule
  expandLeft (phi `Impl` psi) = simpleExp [fromAnte [psi], fromCons [phi]] ImplL
  expandLeft (phi `Disj` psi) = (simpleExp . fmap fromAnte) [[phi], [psi]] DisL
  expandLeft (phi `Conj` psi) = simpleExp [fromAnte [phi, psi]] ConL
  expandLeft (Neg phi) = simpleExp [fromCons [phi]] NegL
  expandLeft phi@(P _) = Atomic phi
  expandLeft phi@Top = Atomic phi
  expandLeft phi@Bot = Atomic phi

  expandRight :: PropForm p -> Expansion SimpleSequent (PropForm p) PropRule
  expandRight (phi `Impl` psi) = simpleExp [S [phi] [psi]] ImplR
  expandRight (phi `Conj` psi) = simpleExp [fromCons [psi], fromCons [phi]] ConR
  expandRight (phi `Disj` psi) = simpleExp [fromCons [phi, psi]] DisR
  expandRight (Neg phi) = simpleExp [fromAnte [phi]] NegR
  expandRight phi@(P _) = Atomic phi
  expandRight phi@Top = Atomic phi
  expandRight phi@Bot = Atomic phi

instance (Eq p) => Verfiable (PropForm p) where
  verifyAxiom :: SimpleSequent (PropForm p) -> Bool
  verifyAxiom (S a c) = (Bot `elem` a) || (Top `elem` c) || (not . null) (a `intersect` c)

  formSimple :: PropForm p -> Bool
  formSimple (P _) = True
  formSimple Top = True
  formSimple Bot = True
  formSimple _ = False
\end{code}
We also implement the Arbitrary class in order to perform tests.
\begin{code}
instance (Arbitrary p) => Arbitrary (PropForm p) where
  arbitrary = sized f
    where
      f 0 = P <$> arbitrary
      f n =
        oneof
          [ Neg <$> f (n - 1),
            Impl
              <$> f (n `div` 3)
              <*> f (n `div` 3),
            Conj <$> f (n `div` 3) <*> f (n `div` 3),
            Disj <$> f (n `div` 3) <*> f (n `div` 3)
          ]
\end{code}

\begin{code}
instance ToLatex PropRule where
  toLatex ConL = "\\(\\wedge L\\)"
  toLatex ConR = "\\(\\wedge R\\)"
  toLatex DisL = "\\(\\vee L\\)"
  toLatex DisR = "\\(\\vee R\\)"
  toLatex NegL = "\\(\\neg L\\)"
  toLatex NegR = "\\(\\neg R\\)"
  toLatex ImplL = "\\(\\to L\\)"
  toLatex ImplR = "\\(\\to R\\)"

instance ToLatex p => ToLatex (PropForm p) where
  toLatex (P p) = "p_{" ++ toLatex p ++ "}"
  toLatex Top = "\\top "
  toLatex Bot = "\\bot "
  toLatex (Conj phi psi) = "(" ++ toLatex phi ++ ")" ++ "\\wedge " ++ "(" ++ toLatex psi ++ ")"
  toLatex (Disj phi psi) = "(" ++ toLatex phi ++ ")" ++ "\\vee " ++ "(" ++ toLatex psi ++ ")"
  toLatex (Impl phi psi) = "(" ++ toLatex phi ++ ")" ++ "\\to " ++ "(" ++ toLatex psi ++ ")"
  toLatex (Neg phi) = "\\neg " ++ "(" ++ toLatex phi ++ ")"
\end{code}

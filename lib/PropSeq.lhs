\ignore{
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
      Sequent(..),
      SimpleSequent(S),
      SequentTree,
      Verifiable(..) )
import Test.QuickCheck (Arbitrary (arbitrary), oneof, sized)
import Latex
\end{code}
}
\subsection{Propositional logic}

The language of propositional logic should be familiar to everyone. It can be
expressed in a Context Free Grammar as such:
\[
    \varphi=P\mid\varphi\vee\varphi\mid\varphi\wedge\varphi\mid\varphi\to\varphi\mid\neg\varphi
\]
where \(P\) is any set of propositional letters. In Haskell we implement it as a
data type generic over a type \(p\) which is the type of the propositional
letters.

% TODO: cite inversion lemma to argue that greedy search works.

\begin{code}
data PropForm p
  = P p
  | Neg (PropForm p)
  | Conj (PropForm p) (PropForm p)
  | Disj (PropForm p) (PropForm p)
  | Impl (PropForm p) (PropForm p)
  | Bot
  | Top
  deriving (Eq, Show)

type PSequent p = SimpleSequent (PropForm p)

type PSeqTree p = SequentTree SimpleSequent (PropForm p) PropRule

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
    \label{fig:tauto2}
\end{figure}

We implement the types from the sequent module in order to use its functions to
create proofs. This is simply according to the definition of sequent calculus
above.
\begin{code}
data PropRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

instance (Eq p) => Verifiable (PropForm p) where
  verifyAxiom :: Sequent s => s (PropForm p) -> Bool
  verifyAxiom s = (Bot `elem` a) || (Top `elem` c) || (not . null) (a `intersect` c)
    where
      a = ante s
      c = cons s

instance Eq p => Expandable SimpleSequent (PropForm p) PropRule where
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
\end{code}
We also implement the Arbitrary class in order to perform tests.
\begin{code}
instance (Arbitrary p) => Arbitrary (PropForm p) where
  arbitrary = sized f
    where
      f 0 = P <$> arbitrary
      f n =
        oneof
          [ Neg <$> f (n `div` 2),
            Impl
              <$> f (n `div` 8)
              <*> f (n `div` 8),
            Conj <$> f (n `div` 8) <*> f (n `div` 8),
            Disj <$> f (n `div` 8) <*> f (n `div` 8)
          ]
\end{code}

We also implement printing a formula as LaTeX expression in order to export
our generated proofs. We do a bit of work to eliminate as many parentheses as
possible. We do this by checking whether operators bind stronger or weaker and
deciding whether parentheses are necessary based on this.

\begin{code}
instance ToLatex PropRule where
  toLatex ConL = "\\wedge L"
  toLatex ConR = "\\wedge R"
  toLatex DisL = "\\vee L"
  toLatex DisR = "\\vee R"
  toLatex NegL = "\\neg L"
  toLatex NegR = "\\neg R"
  toLatex ImplL = "\\to L"
  toLatex ImplR = "\\to R"

isCon :: PropForm p -> Bool
isCon (Conj _ _) = True
isCon _ = False

isDis :: PropForm p -> Bool
isDis (Disj _ _) = True
isDis _ = False

isNeg :: PropForm p -> Bool
isNeg (Neg _) = True
isNeg _ = False

isAtom :: PropForm p -> Bool
isAtom (P _) = True
isAtom Bot = True
isAtom Top = True
isAtom _ = False

instance ToLatex p => ToLatex (PropForm p) where
  toLatex (P p) = "p_{" ++ toLatex p ++ "}"
  toLatex Top = "\\top "
  toLatex Bot = "\\bot "
  toLatex (Conj phi psi) = leftForm ++ "\\wedge " ++ rightForm
    where
      leftForm = if any ($ phi) [isCon, isNeg, isAtom] then toLatex phi else "(" ++ toLatex phi ++ ")"
      rightForm = if any ($ psi) [isCon, isNeg, isAtom] then toLatex psi else "(" ++ toLatex psi ++ ")"


  toLatex (Disj phi psi) = leftForm ++ "\\vee " ++ rightForm
    where
      leftForm = if any ($ phi) [isDis, isNeg, isAtom] then toLatex phi else "(" ++ toLatex phi ++ ")"
      rightForm = if any ($ psi) [isDis, isNeg, isAtom] then toLatex psi else "(" ++ toLatex psi ++ ")"


  toLatex (Impl phi psi) = leftForm ++ "\\to " ++ rightForm
    where
      leftForm = if any ($ phi) [isDis, isCon, isNeg, isAtom] then toLatex phi else "(" ++ toLatex phi ++ ")"
      rightForm = if any ($ psi) [isDis, isCon, isNeg, isAtom] then toLatex psi else "(" ++ toLatex psi ++ ")"

  toLatex (Neg phi@(Neg _)) = "\\neg " ++ toLatex phi
  toLatex (Neg phi@(P _)) = "\\neg " ++ toLatex phi
  toLatex (Neg phi) = "\\neg " ++ "(" ++ toLatex phi ++ ")"
\end{code}

Our code can easily now easily produce proofs of simple and more complex
sequents. For example evaluating
\begin{verbatim}
putStr $ toLatex $ head $ allValidTrees (S [Neg $ Neg $ P (0::Int)] [P 0])
\end{verbatim}
will yield a piece of code that renders the following proof tree:
\[
\begin{prooftree}\hypo{p_{0}\Rightarrow p_{0}}
\infer1[\(\neg R\)]{\Rightarrow p_{0},\neg p_{0}}

\infer1[\(\neg L\)]{\neg\neg p_{0}\Rightarrow p_{0}}
\end{prooftree}
\]

Trying something more complicated, for example the sequent from
\Cref{fig:tauto2} we get:
\[
\begin{prooftree}
\hypo{p_{1},p_{1}\Rightarrow p_{1}}
\hypo{p_{1},p_{0}\Rightarrow p_{1}}
\infer1[\(\neg R\)]{p_{1}\Rightarrow p_{1},\neg p_{0}}

\infer2[\(\to L\)]{p_{1},\neg p_{0}\to p_{1}\Rightarrow p_{1}}

\infer1[\(\to R\)]{p_{1}\Rightarrow (\neg p_{0}\to p_{1})\to p_{1}}

\hypo{p_{1}\Rightarrow p_{0},p_{1}}
\hypo{p_{0}\Rightarrow p_{0},p_{1}}
\infer1[\(\neg R\)]{\Rightarrow p_{0},p_{1},\neg p_{0}}

\infer2[\(\to L\)]{\neg p_{0}\to p_{1}\Rightarrow p_{0},p_{1}}

\infer1[\(\to R\)]{\Rightarrow (\neg p_{0}\to p_{1})\to p_{1},p_{0}}

\infer2[\(\to L\)]{p_{0}\to p_{1}\Rightarrow (\neg p_{0}\to p_{1})\to p_{1}}

\infer1[\(\to R\)]{\Rightarrow (p_{0}\to p_{1})\to ((\neg p_{0}\to p_{1})\to p_{1})}

\end{prooftree}
\]

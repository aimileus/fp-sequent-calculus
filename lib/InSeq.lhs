\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module InSeq where

import PropSeq (PropForm (..))
import Sequent
import Data.List
import Latex

newtype InForm p = In (PropForm p) deriving (Show, Eq)

data InRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

instance Eq p => Expandable SimpleSequent (InForm p) InRule where
  expandLeft :: Eq p => InForm p -> Expansion SimpleSequent (InForm p) InRule
  expandLeft (In (phi `Impl` psi)) = simpleExp [fromAnte [In psi], fromCons [In phi]] ImplL
  expandLeft (In (phi `Disj` psi)) = (simpleExp . fmap fromAnte) [[In phi], [In psi]] DisL
  expandLeft (In (phi `Conj` psi)) = simpleExp [fromAnte [In phi, In psi]] ConL
  expandLeft (In (Neg phi)) = simpleExp [fromAnte [In (phi `Impl` Bot)]] NegL
  expandLeft phi@(In (P _)) = Atomic phi
  expandLeft phi@(In Top) = Atomic phi
  expandLeft phi@(In Bot) = Atomic phi

  expandRight :: Eq p => InForm p -> Expansion SimpleSequent (InForm p) InRule
  expandRight (In (phi `Impl` psi)) = Exp mergeRightImpl [S [In phi] [In psi]] ImplR
  expandRight (In (phi `Conj` psi)) = simpleExp [fromCons [In psi], fromCons [In phi]] ConR
  expandRight (In (phi `Disj` psi)) = simpleExp [fromCons [In phi, In psi]] DisR
  expandRight (In (Neg phi)) = simpleExp [fromCons [In phi]] NegR
  expandRight phi@(In (P _)) = Atomic phi
  expandRight phi@(In Top) = Atomic phi
  expandRight phi@(In Bot) = Atomic phi


instance (Eq p) => Verifiable (InForm p) where
  verifyAxiom :: Sequent s => s (InForm p) -> Bool
  verifyAxiom s = (In Bot `elem` a) || (In Top `elem` c) || (not . null) (a `intersect` c)
    where
      a = ante s
      c = cons s

  formSimple (In phi) = formSimple phi

mergeRightImpl :: Eq a => SimpleSequent a -> SimpleSequent a -> SimpleSequent a
mergeRightImpl (S a1 _c1) (S a2 c2) = S (nub (a1 ++ a2)) c2

instance ToLatex InRule where
  toLatex ConL = "\\(\\wedge L\\)"
  toLatex ConR = "\\(\\wedge R\\)"
  toLatex DisL = "\\(\\vee L\\)"
  toLatex DisR = "\\(\\vee R\\)"
  toLatex NegL = "\\(\\neg L\\)"
  toLatex NegR = "\\(\\neg R\\)"
  toLatex ImplL = "\\(\\to L\\)"
  toLatex ImplR = "\\(\\to R\\)"

instance ToLatex p => ToLatex (InForm p) where
  toLatex (In phi) = toLatex phi


\end{code}

\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module InSeq where

import PropSeq (PropForm (..))
import Sequent

newtype InForm p = In (PropForm p)

data InRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

instance Expandable (InForm p) InRule where
  expandLeft :: InForm p -> Expansion (InForm p) InRule
  expandLeft (In (phi `Impl` psi)) = simpleExp [fromAnte [In psi], fromCons [In phi]] ImplL
  expandLeft (In (phi `Disj` psi)) = (simpleExp . fmap fromAnte) [[In phi], [In psi]] DisL
  expandLeft (In (phi `Conj` psi)) = simpleExp [fromAnte [In phi, In psi]] ConL
  expandLeft (In (Neg phi)) = simpleExp [fromAnte [In (phi `Impl` Bot)]] NegL
  expandLeft phi@(In (P _)) = AtomicL phi
  expandLeft phi@(In Top) = AtomicL phi
  expandLeft phi@(In Bot) = AtomicL phi

  expandRight :: InForm p -> Expansion (InForm p) InRule
  expandRight (In (phi `Impl` psi)) = Exp mergeRightImpl [S [In phi] [In psi]] ImplR
  expandRight (In (phi `Conj` psi)) = simpleExp [fromCons [In psi], fromCons [In phi]] ConR
  expandRight (In (phi `Disj` psi)) = simpleExp [fromCons [In phi, In psi]] DisR
  expandRight (In (Neg phi)) = simpleExp [fromCons [In phi]] NegR
  expandRight phi@(In (P _)) = AtomicR phi
  expandRight phi@(In Top) = AtomicR phi
  expandRight phi@(In Bot) = AtomicR phi

mergeRightImpl :: Sequent a -> Sequent a -> Sequent a
mergeRightImpl (S a1 _c1) (S a2 c2) = S (a1 ++ a2) c2

\end{code}
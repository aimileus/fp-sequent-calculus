{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module PropSeq where

import Sequent

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

data PropRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

instance Expandable (PropForm p) PropRule where
  expandLeft :: PropForm p -> Expansion (PropForm p) PropRule
  expandLeft (phi `Impl` psi) = simpleExp [fromAnte [psi], fromCons [phi]] ImplL
  expandLeft (phi `Disj` psi) = (simpleExp . fmap fromAnte) [[phi], [psi]] DisL
  expandLeft (phi `Conj` psi) = simpleExp [fromAnte [phi, psi]] ConL
  expandLeft (Neg phi) = simpleExp [fromCons [phi]] NegL
  expandLeft phi@(P _) = AtomicL phi
  expandLeft phi@Top = AtomicL phi
  expandLeft phi@Bot = AtomicL phi

  expandRight :: PropForm p -> Expansion (PropForm p) PropRule
  expandRight (phi `Impl` psi) = simpleExp [S [phi] [psi]] ImplR
  expandRight (phi `Conj` psi) = simpleExp [fromCons [psi], fromCons [phi]] ConR
  expandRight (phi `Disj` psi) = simpleExp [fromCons [phi, psi]] DisR
  expandRight (Neg phi) = simpleExp [fromAnte [phi]] NegR
  expandRight phi@(P _) = AtomicR phi
  expandRight phi@Top = AtomicR phi
  expandRight phi@Bot = AtomicR phi

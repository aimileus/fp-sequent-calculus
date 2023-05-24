module InSeq where

import PropSeq (PropForm (..))
import Sequent

data InRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

instance Expandable (PropForm p) InRule where
  expandLeft :: PropForm p -> Expansion (PropForm p) InRule
  expandLeft (phi `Impl` psi) = simpleExp [fromAnte [psi], fromCons [phi]] ImplL
  expandLeft (phi `Disj` psi) = (simpleExp . fmap fromAnte) [[phi], [psi]] DisL
  expandLeft (phi `Conj` psi) = simpleExp [fromAnte [phi, psi]] ConL
  expandLeft (Neg phi) = simpleExp [fromAnte [phi `Impl` Bot]] NegL
  expandLeft phi@(P _) = AtomicL phi
  expandLeft phi@Top = AtomicL phi
  expandLeft phi@Bot = AtomicL phi

  expandRight :: PropForm p -> Expansion (PropForm p) InRule
  expandRight (phi `Impl` psi) = Exp mergeRightImpl [S [phi] [psi]] ImplR
  expandRight (phi `Conj` psi) = simpleExp [fromCons [psi], fromCons [phi]] ConR
  expandRight (phi `Disj` psi) = simpleExp [fromCons [phi, psi]] DisR
  expandRight (Neg phi) = simpleExp [fromCons [phi]] NegR
  expandRight phi@(P _) = AtomicR phi
  expandRight phi@Top = AtomicR phi
  expandRight phi@Bot = AtomicR phi

mergeRightImpl :: Sequent (PropForm p) -> Sequent (PropForm p) -> Sequent (PropForm p)
mergeRightImpl (S a1 _c1) (S a2 c2) = S (a1 ++ a2) c2

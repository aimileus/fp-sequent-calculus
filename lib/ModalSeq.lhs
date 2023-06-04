\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ModalSeq where

import PropSeq
import Sequent

data ModalForm p = Dia (ModalForm p) | Box (ModalForm p) | Prop (PropForm p)

data ModalRule = DiaL | DiaR | BoxL | BoxR | PropR PropRule

seqPropToModal :: SimpleSequent (PropForm p) -> SimpleSequent (ModalForm p)
seqPropToModal (S a c) = S (Prop <$> a) (Prop <$> c)

expPropToModal :: Expansion SimpleSequent (PropForm p) PropRule -> Expansion SimpleSequent (ModalForm p) ModalRule
expPropToModal = undefined
-- expPropToModal (Exp m e r) = Exp m (seqPropToModal <$> e) (PropR r)
-- expPropToModal (Atomic f) = Atomic (Prop f)


instance Eq p => Verifiable (ModalForm p) where
  verifyAxiom = undefined

instance (Eq p) => Expandable SimpleSequent (ModalForm p) ModalRule where
  expandLeft :: ModalForm p -> Expansion SimpleSequent (ModalForm p) ModalRule
  expandLeft (Dia _f) = undefined
  expandLeft (Box _f) = undefined
  expandLeft (Prop f) = expPropToModal $ expandLeft f

  expandRight :: ModalForm p -> Expansion SimpleSequent (ModalForm p) ModalRule
  expandRight (Dia _f) = undefined
  expandRight (Box _f) = undefined
  expandRight (Prop f) = expPropToModal $ expandRight f

\end{code}

\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ModalSeq where

import PropSeq
import Sequent

data ModalForm p = Dia (ModalForm p) | Box (ModalForm p) | Prop (PropForm p)

data ModalRule = DiaL | DiaR | BoxL | BoxR | PropR PropRule

seqPropToModal :: Sequent (PropForm p) -> Sequent (ModalForm p)
seqPropToModal (S a c) = S (Prop <$> a) (Prop <$> c)

expPropToModal :: Expansion (PropForm p) PropRule -> Expansion (ModalForm p) ModalRule
expPropToModal (Exp m e r) = Exp m (seqPropToModal <$> e) (PropR r)
expPropToModal (AtomicL f) = AtomicL (Prop f)
expPropToModal (AtomicR f) = AtomicR (Prop f)

instance Expandable (ModalForm p) ModalRule where
  expandLeft :: ModalForm p -> Expansion (ModalForm p) ModalRule
  expandLeft (Dia _f) = undefined
  expandLeft (Box _f) = undefined
  expandLeft (Prop f) = expPropToModal $ expandLeft f

  expandRight :: ModalForm p -> Expansion (ModalForm p) ModalRule
  expandRight (Dia _f) = undefined
  expandRight (Box _f) = undefined
  expandRight (Prop f) = expPropToModal $ expandRight f

\end{code}
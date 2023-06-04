\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module ModalSeq where

import PropSeq
import Sequent
import Data.List

data ModalForm p = Dia (ModalForm p) | Box (ModalForm p) | Prop (PropForm p) deriving (Eq, Show)

data ModalRule = DiaL | DiaR | BoxL | BoxR | PropR PropRule

seqPropToModal :: SimpleSequent (PropForm p) -> SimpleSequent (ModalForm p)
seqPropToModal (S a c) = S (Prop <$> a) (Prop <$> c)

expPropToModal :: Expansion SimpleSequent (PropForm p) PropRule -> Expansion SimpleSequent (ModalForm p) ModalRule
expPropToModal (Exp _m e r) = Exp simpleMerge (seqPropToModal <$> e) (PropR r)
expPropToModal (Atomic f) = Atomic (Prop f)

isDia :: ModalForm p -> Bool
isDia (Dia _) = True
isDia _ = False

isBox :: ModalForm p -> Bool
isBox (Box _) = True
isBox _ = False

mergeOnly :: (ModalForm p -> Bool) ->  SimpleSequent (ModalForm p) -> SimpleSequent (ModalForm p) -> SimpleSequent (ModalForm p)
mergeOnly f (S a1 c1) (S a2 c2) = S (a1 ++ filter f a2) (c1 ++ filter f c2)

instance Eq p => Verifiable (ModalForm p) where
  verifyAxiom = undefined

instance (Eq p) => Expandable SimpleSequent (ModalForm p) ModalRule where
  expandLeft :: ModalForm p -> Expansion SimpleSequent (ModalForm p) ModalRule
  expandLeft (Dia f) = Exp (mergeOnly isDia) [S [f] []] DiaL
  expandLeft (Box f) = Exp simpleMerge [S [f] []] BoxL
  expandLeft (Prop f) = expPropToModal $ expandLeft f

  expandRight :: ModalForm p -> Expansion SimpleSequent (ModalForm p) ModalRule
  expandRight (Dia f) = Exp simpleMerge [S [] [f]] DiaR
  expandRight (Box f) = Exp (mergeOnly isBox) [S [] [f]] BoxR
  expandRight (Prop f) = expPropToModal $ expandRight f

instance (Eq p) => Verifiable (ModalForm p) where
  verifyAxiom :: Sequent s => s (ModalForm p) -> Bool
  verifyAxiom s = (Prop Bot `elem` a) || (Prop Top `elem` c) || (not . null) (a `intersect` c)
    where
      a = ante s
      c = cons s

  formSimple :: Eq p => ModalForm p -> Bool
  formSimple (Dia f) = formSimple f
  formSimple (Box f) = formSimple f
  formSimple (Prop f) = formSimple f
\end{code}

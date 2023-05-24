{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Sequent where

import Data.List
import Data.Maybe

type Prop = Int

data PropForm p
  = P p
  | Neg (PropForm p)
  | Conj (PropForm p) (PropForm p)
  | Disj (PropForm p) (PropForm p)
  | Impl (PropForm p) (PropForm p)
  deriving (Eq, Show)

data Sequent f = S
  { ante :: [f],
    cons :: [f]
  }
  deriving (Eq, Show)

data PropRule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

data SequentTree f r
  = Axiom (Sequent f)
  | Application r (Sequent f) [SequentTree f r]
  deriving (Eq, Show)

isProp :: PropForm p -> Bool
isProp (P _) = True
isProp _ = False

simple :: Sequent (PropForm p) -> Bool
simple s = all (all isProp) [ante s, cons s]

axiom :: (Eq f) => Sequent f -> Bool
axiom s = not . null $ ante s `intersect` cons s

mergeSequent :: Sequent p -> Sequent p -> Sequent p
mergeSequent (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

fromAnte :: [f] -> Sequent f
fromAnte fs = S fs []

fromCons :: [f] -> Sequent f
fromCons = S []

data Expansion f r
  = Exp
      { exps :: [Sequent f],
        rule :: r
      }
  | AtomicL f
  | AtomicR f

data Expanded f r = Expd
  { expds :: [Sequent f],
    rule' :: r
  }

class Expandable f r where
  expandLeft :: f -> Expansion f r
  expandRight :: f -> Expansion f r

instance Expandable (PropForm p) PropRule where
  expandLeft :: PropForm p -> Expansion (PropForm p) PropRule
  expandLeft (phi `Impl` psi) = Exp [fromAnte [psi], fromCons [phi]] ImplL
  expandLeft (phi `Disj` psi) = (Exp . fmap fromAnte) [[phi], [psi]] DisL
  expandLeft (phi `Conj` psi) = Exp [fromAnte [phi, psi]] ConL
  expandLeft (Neg phi) = Exp [fromCons [phi]] NegL
  expandLeft phi@(P _) = AtomicL phi

  expandRight :: PropForm p -> Expansion (PropForm p) PropRule
  expandRight (phi `Impl` psi) = Exp [S [phi] [psi]] ImplR
  expandRight (phi `Conj` psi) = Exp [fromCons [psi], fromCons [phi]] ConR
  expandRight (phi `Disj` psi) = Exp [fromCons [phi, psi]] DisR
  expandRight (Neg phi) = Exp [fromCons [phi]] NegR
  expandRight phi@(P _) = AtomicR phi

applyExpansion :: Sequent f -> Expansion f r -> Maybe (Expanded f r)
applyExpansion s (Exp e r) = Just $ Expd (mergeSequent s <$> e) r
applyExpansion _ (AtomicL _) = Nothing
applyExpansion _ (AtomicR _) = Nothing

-- Is dit wat je wil, want de SeqTree die je moet maken is wel anders in deze twee gevallen.
-- Ik comment dit even, want ik heb hem net anders in m'n hoofd nu, even kijken of het logisch uitkomt
-- applyExpansion (AtomicL f) = [fromAnte f]
-- applyExpansion (AtomicR f) = [fromCons f]

isAtomic :: Expansion f r -> Bool
isAtomic (AtomicL _) = True
isAtomic (AtomicR _) = True
isAtomic _ = False

-- TODO: use zipper lists here instead of this mildly computationally intensive way.
extractForm :: (Expandable f r) => Sequent f -> [(Sequent f, Expansion f r)]
extractForm (S l r) = lefts ++ rights
  where
    lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
    rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)

holes :: [a] -> [([a], a)]
holes [] = []
holes (x : xs) = (xs, x) : fmap (mapFst (x :)) (holes xs)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = fmap

prove :: (Expandable f r) => Sequent f -> SequentTree f r
prove s = tree expanded
  where
    expanded = listToMaybe $ mapMaybe (uncurry applyExpansion) (extractForm s)

    tree Nothing = Axiom s
    tree (Just (Expd e r)) = Application r s (prove <$> e)

verifyTree :: (Eq f) => SequentTree f r -> Bool
verifyTree (Axiom (S ante cons)) = (not . null) (ante `intersect` cons)
verifyTree (Application _ _ ys) = all verifyTree ys

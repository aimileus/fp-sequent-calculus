{-# LANGUAGE ImpredicativeTypes #-}

module Sequent where

import Data.List
import Data.Maybe

type Prop = Int

data Formula p
  = P p
  | Neg (Formula p)
  | Conj (Formula p) (Formula p)
  | Disj (Formula p) (Formula p)
  | Impl (Formula p) (Formula p)
  deriving (Eq, Show)

type PropFormula = Formula Prop

data Sequent f = S
  { ante :: [f],
    cons :: [f]
  }
  deriving (Eq, Show)

data Rule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

data SequentTree f
  = Axiom (Sequent f)
  | Application Rule (Sequent f) [SequentTree f]
  deriving (Eq, Show)

isProp :: Formula p -> Bool
isProp (P _) = True
isProp _ = False

simple :: Sequent (Formula p) -> Bool
simple s = all (all isProp) [ante s, cons s]

axiom :: (Eq f) => Sequent f -> Bool
axiom s = not . null $ ante s `intersect` cons s

mergeSequent :: Sequent p -> Sequent p -> Sequent p
mergeSequent (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

fromAnte :: [f] -> Sequent f
fromAnte fs = S fs []

fromCons :: [f] -> Sequent f
fromCons = S []

data Expansion f
  = Exp
      { exps :: [Sequent f],
        rule :: Rule
      }
  | AtomicL f
  | AtomicR f

data Expanded f = Expd
  { expds :: [Sequent f],
    rule' :: Rule
  }

applyExpansion :: Sequent f -> Expansion f -> Maybe (Expanded f)
applyExpansion s (Exp e r) = Just $ Expd (mergeSequent s <$> e) r
applyExpansion _ (AtomicL _) = Nothing
applyExpansion _ (AtomicR _) = Nothing

-- Is dit wat je wil, want de SeqTree die je moet maken is wel anders in deze twee gevallen.
-- Ik comment dit even, want ik heb hem net anders in m'n hoofd nu, even kijken of het logisch uitkomt
-- applyExpansion (AtomicL f) = [fromAnte f]
-- applyExpansion (AtomicR f) = [fromCons f]

isAtomic :: Expansion f -> Bool
isAtomic (AtomicL _) = True
isAtomic (AtomicR _) = True
isAtomic _ = False

expandLeft :: Formula p -> Expansion (Formula p)
expandLeft (phi `Impl` psi) = Exp [fromAnte [psi], fromCons [phi]] ImplL
expandLeft (phi `Disj` psi) = (Exp . fmap fromAnte) [[phi], [psi]] DisL
expandLeft (phi `Conj` psi) = Exp [fromAnte [phi, psi]] ConL
expandLeft (Neg phi) = Exp [fromCons [phi]] NegL
expandLeft phi@(P _) = AtomicL phi

expandRight :: Formula p -> Expansion (Formula p)
expandRight (phi `Impl` psi) = Exp [S [phi] [psi]] ImplR
expandRight (phi `Conj` psi) = Exp [fromCons [psi], fromCons [phi]] ConR
expandRight (phi `Disj` psi) = Exp [fromCons [phi, psi]] DisR
expandRight (Neg phi) = Exp [fromCons [phi]] NegR
expandRight phi@(P _) = AtomicR phi

-- TODO: use zipper lists here instead of this mildly computationally intensive way.
extractFormula :: Sequent (Formula p) -> [(Sequent (Formula p), Expansion (Formula p))]
extractFormula (S l r) = lefts ++ rights
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

prove :: Sequent (Formula p) -> SequentTree (Formula p)
prove s = tree expanded
  where
    expanded = listToMaybe $ mapMaybe (uncurry applyExpansion) (extractFormula s)

    tree Nothing = Axiom s
    tree (Just (Expd e r)) = Application r s (prove <$> e)

verifyTree :: (Eq f) => SequentTree f -> Bool
verifyTree (Axiom (S ante cons)) = (not . null) (ante `intersect` cons)
verifyTree (Application _ _ ys) = all verifyTree ys

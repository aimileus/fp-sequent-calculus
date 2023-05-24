{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Sequent where

import Data.List
import Data.Maybe
import Utils

data Sequent f = S
  { ante :: [f],
    cons :: [f]
  }
  deriving (Eq, Show)

data SequentTree f r
  = Axiom (Sequent f)
  | Application r (Sequent f) [SequentTree f r]
  deriving (Eq, Show)

axiom :: (Eq f) => Sequent f -> Bool
axiom s = not . null $ ante s `intersect` cons s

simpleMerge :: Sequent p -> Sequent p -> Sequent p
simpleMerge (S fs ps) (S fs' ps') = S (fs ++ fs') (ps ++ ps')

simpleExp :: [Sequent f] -> r -> Expansion f r
simpleExp = Exp simpleMerge

fromAnte :: [f] -> Sequent f
fromAnte fs = S fs []

fromCons :: [f] -> Sequent f
fromCons = S []

data Expansion f r
  = Exp
      { merge :: forall a. Sequent a -> Sequent a -> Sequent a,
        exps :: [Sequent f],
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

applyExpansion :: Sequent f -> Expansion f r -> Maybe (Expanded f r)
applyExpansion s (Exp m e r) = Just $ Expd (m s <$> e) r
applyExpansion _ (AtomicL _) = Nothing
applyExpansion _ (AtomicR _) = Nothing

-- TODO: use zipper lists here instead of this mildly computationally intensive way.
extractForm :: (Expandable f r) => Sequent f -> [(Sequent f, Expansion f r)]
extractForm (S l r) = lefts ++ rights
  where
    lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
    rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)

prove :: (Expandable f r) => Sequent f -> SequentTree f r
prove s = tree expanded
  where
    expanded = listToMaybe $ mapMaybe (uncurry applyExpansion) (extractForm s)

    tree Nothing = Axiom s
    tree (Just (Expd e r)) = Application r s (prove <$> e)

verifyTree :: (Eq f) => SequentTree f r -> Bool
verifyTree (Axiom (S ante cons)) = (not . null) (ante `intersect` cons)
verifyTree (Application _ _ ys) = all verifyTree ys

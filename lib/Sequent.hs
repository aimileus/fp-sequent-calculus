{-# LANGUAGE ImpredicativeTypes #-}

module Sequent where

import Data.List

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

data SeqTree f = ST
  { seq :: Sequent f,
    children :: [Sequent f]
  }
  deriving (Eq, Show)

data Rule = ConL | ConR | DisL | DisR | NegL | NegR | ImplL | ImplR
  deriving (Eq, Show, Enum)

data SequentTree f
  = Axiom (Sequent f)
  | Application Rule [Sequent f]

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
  | Atomic f

isAtomic :: Expansion f -> Bool
isAtomic (Atomic _) = True
isAtomic _ = False

simpleExpand :: Formula p -> Formula p -> Rule -> [Expansion (Formula p)]
simpleExpand f g r = fmap ($ r) [Exp (return $ fromAnte [f]), Exp (return $ fromCons [g])]

expandHelper :: Rule -> Sequent (Formula p) -> Expansion (Formula p)
expandHelper r s = Exp [s] r

expandLeft :: Formula p -> [Expansion (Formula p)]
expandLeft (phi `Impl` psi) = fmap (expandHelper ImplL) [fromAnte [psi], fromCons [phi]]
expandLeft (phi `Disj` psi) = fmap (expandHelper DisL . fromAnte) [[phi], [psi]]
expandLeft (phi `Conj` psi) = fmap (expandHelper ConL . fromAnte) [[phi, psi]]
expandLeft (Neg phi) = fmap (expandHelper NegL . fromCons) [[phi]]
expandLeft phi@(P _) = [Atomic phi]

expandRight :: Formula p -> [Expansion (Formula p)]
expandRight (phi `Impl` psi) = [Exp [fromCons [phi], fromAnte [psi]] ImplL]
expandRight (phi `Conj` psi) =
  fmap
    ($ ConR)
    [ Exp [fromCons [phi]],
      Exp [fromCons [psi]]
    ]
expandRight (phi `Disj` psi) = [Exp [fromCons [phi, psi]] DisR]
expandRight (Neg phi) = [Exp [fromCons [phi]] NegR]
expandRight phi@(P _) = [Atomic phi]

-- TODO: use zipper lists here instead of this mildly computationally intensive way.
extractFormula :: Sequent (Formula p) -> [(Sequent (Formula p), Expansion (Formula p))]
extractFormula (S l r) = undefined
  where
    -- lefts :: [(Sequent (Formula p), [Expansion (Formula p)])]
    lefts = fmap (mapFst (`S` r) . mapSnd expandLeft) (holes l)
    -- rights :: [(Sequent (Formula p), [Expansion (Formula p)])]
    rights = fmap (mapFst (S l) . mapSnd expandRight) (holes r)

holes :: [a] -> [([a], a)]
holes [] = []
holes (x : xs) = (xs, x) : fmap (mapFst (x :)) (holes xs)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = fmap

proveStep :: Sequent f -> [Sequent f]
proveStep = undefined

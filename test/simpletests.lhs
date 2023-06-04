\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Main where

import Utils ( combs, holes, firstJust )
import Sequent
    ( Sequent(..),
      SimpleSequent(..),
      simpleMerge,
      fromAnte,
      fromCons,
      seqSimple,
      leafs,
      greedyTree,
      verifyTree,
      simple2zipper,
      zipper2simple,
      prove,
      )
import PropSeq
import InSeq

import Data.List

import Test.Hspec
import Test.QuickCheck
import Data.Maybe (isJust, isNothing)
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

\begin{code}
validForms :: [PropForm Int]
validForms =
  [
    P 1 `Disj` Neg (P 1),
    Neg (P 1 `Conj` Neg (P 1)),
    Top,
    ((P 1 `Impl` P 2) `Conj` (P 2 `Impl` P 3)) `Impl` (P 1 `Impl` P 3)
  ]

validSeqs :: [PSequent Int]
validSeqs = [
    S [Neg $ Neg $ P 1] [P 1],
    S [P 1 `Disj` P 2] [P 1, P 2],
    S [P 1, P 2] [P 1 `Conj` P 2],
    S [P 1, P 2] [P 1, P 2]
  ] ++ map (fromCons . return) validForms

invalidForms :: [PropForm Int]
invalidForms = [
    P 1,
    P 1 `Conj` P 2,
    P 1 `Impl` Neg (P 1),
    Bot
  ]

invalidSeqs :: [PSequent Int]
invalidSeqs = [
    S [] [P 1, P 2],
    S [P 1 `Disj` P 2] [P 1]
  ] ++ map (fromCons . return) invalidForms

fromCons' :: [f] -> SimpleSequent f
fromCons' = fromCons

fromAnte' :: [f] -> SimpleSequent f
fromAnte' = fromAnte

main :: IO ()
main = hspec $ do
  describe "SimpleSequent" $ do
    it "fromAnte: cons should be empty" $
      property (\(fs::[PropForm Int]) -> null $ cons $ fromAnte' fs)
    it "fromAnte: ante is inverse" $
      property (\(fs::[PropForm Int]) -> ante (fromAnte' fs) == fs)
    it "fromCons: ante should be empty" $
      property (\(fs::[PropForm Int]) -> null $ ante $ fromCons' fs)
    it "fromCons: cons is inverse" $
      property (\(fs::[PropForm Int]) -> cons (fromCons' fs) == fs)
  describe "Properties of propositional logic" $ do
    it "valid sequents are valid" $
      all (verifyTree . greedyTree) validSeqs `shouldBe` True
    it "invalid sequents are invalid" $
      any (verifyTree . greedyTree) invalidSeqs `shouldBe` False
    it "seqTree: leafs cannot be simplified" $
      property (\(st::PSeqTree Int) -> all seqSimple $ leafs st)
    it "simpleMerge: ante is merged" $
      property (\(a::PSequent Int) (b::PSequent Int) -> ante a ++ ante b == ante (a `simpleMerge` b))
    it "simpleMerge: cons is merged" $
      property (\(a::PSequent Int) (b::PSequent Int) -> cons a ++ cons b == cons (a `simpleMerge` b))
    it "greedy approach works for classical logic" $
      property (\(a::PSequent Int) -> isJust (prove a) == verifyTree (greedyTree a))
  describe "ZipperSequent" $ do
    it "zipper2simple inverse of simple2zipper:" $
      property (\(s::PSequent Int) -> (zipper2simple . simple2zipper) s == s)
  describe "Intuisionistic logic" $ do
    it "Intuisionistic truth implies classical truth" $
      property (\(s::SimpleSequent (InForm Int)) -> isJust (prove s) <= isJust (prove $ inseq2clas s))
  describe "Utils" $ do
    it "combs: simple test" $
      combs [[1::Int, 2], [3, 4]] `shouldBe` [[1,3],[1,4],[2,3],[2,4]]
    it "combs: slightly advanced test" $
      combs [[1::Int, 2], [3, 4], [5, 6]] `shouldBe` [[1,3,5],[1,3,6],[1,4,5],[1,4,6],[2,3,5],[2,3,6],[2,4,5],[2,4,6]]
    it "combs: length" $
      property (\(xs::[[Int]]) -> not (any null xs) ==> (length . head . combs) xs == length xs)
    it "combs: lazy" $
      (head . combs) [[(1::Int)..], [3..]] `shouldBe` [1,3]
    it "combs: empty combination" $
      combs ([]:map singleton [(1::Int)..]) `shouldBe` []
    it "holes: all elements" $
      property (\(x::[Int]) -> map snd (holes x) == x )
    it "holes: length of list" $
      property (\(x::[Int]) -> all (\y -> length (fst y) + 1 == length x) (holes x))
    it "holes: concat is entire list" $
      property (\(x::[Int]) -> all (\y -> sort (snd y:fst y) == sort x) (holes x))
    it "firstJust: keeps just" $
      property (\(x::[Maybe Int]) -> any isJust x ==> isJust (firstJust x))
    it "firstJust: sees nothing" $
      property (\(x::[Maybe Int]) -> isNothing (firstJust $ filter isNothing x))
    it "firstJust: element of list (when non-empty)" $
      property (\(x::[Maybe Int]) -> null x || firstJust x `elem` x)


\end{code}

To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.

\begin{simplecode}

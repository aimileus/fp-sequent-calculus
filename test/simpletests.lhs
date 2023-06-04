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
      leafs,
      greedyTree,
      verifyTree,
      verifyAxiom,
      prove,
      )
import ZipperSequent
    ( simple2zipper,
      zipper2simple,
      )
import PropSeq
import InSeq
import Latex

import Data.List

import Test.Hspec
import Test.QuickCheck
import Data.Maybe (isJust, isNothing)
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

\begin{code}
p, q, r :: PropForm Int
(p, q, r) = (P 1, P 2, P 3)


validForms :: [PropForm Int]
validForms =
  [
    p `Disj` Neg (p),
    Neg (Neg p) --> p,
    Neg (p & Neg (p)),
    Top,
    ((p --> q) & (q --> r)) --> (p --> r)
  ]

validFormsTex :: [String]
validFormsTex =
  [
    "p_{1}\\vee \\neg p_{1}",
    "\\neg \\neg p_{1}\\to p_{1}",
    "\\neg (p_{1}\\wedge \\neg p_{1})",
    "\\top ",
    "(p_{1}\\to p_{2})\\wedge (p_{2}\\to p_{3})\\to (p_{1}\\to p_{3})"
  ]

validSeqs :: [PSequent Int]
validSeqs = [
    S [Neg (Neg p)] [p],
    S [p `Disj` q] [p, q],
    S [p, q] [p & q],
    S [p, q] [p, q]
  ] ++ map (fromCons . return) validForms

validSeqsTex :: [String]
validSeqsTex =
  [ "\\neg \\neg p_{1}\\Rightarrow p_{1}",
    "p_{1}\\vee p_{2}\\Rightarrow p_{1},p_{2}",
    "p_{1},p_{2}\\Rightarrow p_{1}\\wedge p_{2}",
    "p_{1},p_{2}\\Rightarrow p_{1},p_{2}",
    "\\Rightarrow p_{1}\\vee \\neg p_{1}",
    "\\Rightarrow \\neg \\neg p_{1}\\to p_{1}",
    "\\Rightarrow \\neg (p_{1}\\wedge \\neg p_{1})",
    "\\Rightarrow \\top ",
    "\\Rightarrow (p_{1}\\to p_{2})\\wedge (p_{2}\\to p_{3})\\to (p_{1}\\to p_{3})"
  ]

invalidForms :: [PropForm Int]
invalidForms = [
    p,
    p & q,
    p --> Neg (p),
    Bot
  ]

invalidSeqs :: [PSequent Int]
invalidSeqs = [
    S [] [p, q],
    S [p `Disj` q] [p]
  ] ++ map (fromCons . return) invalidForms


validIForms :: [InForm Int]
validIForms = In <$> [

  ]

invalidIForms :: [InForm Int]
invalidIForms = In <$> [
    p `Disj` Neg p,
    p --> Neg (Neg p)
  ]

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
      property (\(st::PSeqTree Int) -> all (\x -> null (expand x) || verifyAxiom x) $ leafs st)
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
      property (\(s::SimpleSequent (InForm Int)) -> isJust (prove s) <= isJust (prove $ clasSeq s))
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
  describe "Latex" $ do
    it "Formulas get exported properly" $
      toLatex <$> validForms `shouldBe` validFormsTex
    it "Sequents get exported properly" $
      toLatex <$> validSeqs `shouldBe` validSeqsTex
    it "Intuitionistic formulas are formatted the same as normal ones" $
      property (\(x::PropForm Int) -> toLatex (In x) == toLatex x)
\end{code}

To run the tests, use \verb|stack test|.

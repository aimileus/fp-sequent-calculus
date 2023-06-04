\ignore{
\begin{code}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
\end{code}
}
\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Utils ( combs, holes, firstJust )
import Sequent
    ( Sequent(..),
      SimpleSequent(..),
      SequentTree(..),
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

fromAnte' :: [f] -> Sequent.SimpleSequent f
fromAnte' = Sequent.fromAnte

proofTree :: SequentTree SimpleSequent (PropForm Int) PropRule
proofTree = Application PropSeq.ImplR (S [P 1] [Impl (P (0 :: Int)) (Impl (Conj (P 1) (Neg (P 0))) (P 1))]) [Application PropSeq.ImplR (S [P 1, P 0] [Impl (Conj (P 1) (Neg (P 0))) (P 1)]) [Application PropSeq.ConL (S [P 1, P 0, Conj (P 1) (Neg (P 0))] [P 1]) [Application PropSeq.NegL (Sequent.S [P 1, P 0, P 1, Neg (P 0)] [P 1]) [Axiom (S [P 1, P 0, P 1] [P 1, P 0])]]]]

proofTreeTex :: String
proofTreeTex = "\\begin{prooftree}\n\\hypo{p_{1},p_{0},p_{1}\\Rightarrow p_{1},p_{0}}\n\\infer1[\\(\\neg L\\)]{p_{1},p_{0},p_{1},\\neg p_{0}\\Rightarrow p_{1}}\n\n\\infer1[\\(\\wedge L\\)]{p_{1},p_{0},p_{1}\\wedge \\neg p_{0}\\Rightarrow p_{1}}\n\n\\infer1[\\(\\to R\\)]{p_{1},p_{0}\\Rightarrow p_{1}\\wedge \\neg p_{0}\\to p_{1}}\n\n\\infer1[\\(\\to R\\)]{p_{1}\\Rightarrow p_{0}\\to (p_{1}\\wedge \\neg p_{0}\\to p_{1})}\n\n\\end{prooftree}"

main :: IO ()
main = hspec $ do
  describe "SimpleSequent" $ do
    it "fromAnte: cons should be empty" $
      property (\(fs::[PropForm Int]) -> null $ Sequent.cons $ fromAnte' fs)
    it "fromAnte: ante is inverse" $
      property (\(fs::[PropForm Int]) -> Sequent.ante (fromAnte' fs) == fs)
    it "fromCons: ante should be empty" $
      property (\(fs::[PropForm Int]) -> null $ Sequent.ante $ fromCons' fs)
    it "fromCons: cons is inverse" $
      property (\(fs::[PropForm Int]) -> Sequent.cons (fromCons' fs) == fs)
  describe "Properties of propositional logic" $ do
    it "valid sequents are valid" $
      all (Sequent.verifyTree . Sequent.greedyTree) validSeqs `shouldBe` True
    it "invalid sequents are invalid" $
      any (Sequent.verifyTree . Sequent.greedyTree) invalidSeqs `shouldBe` False
    it "seqTree: leafs cannot be simplified" $
      property (\(st::PSeqTree Int) -> all (\x -> null (expand x) || verifyAxiom x) $ leafs st)
    it "simpleMerge: ante is merged" $
      property (\(a::PSequent Int) (b::PSequent Int) -> Sequent.ante a ++ Sequent.ante b == Sequent.ante (a `Sequent.simpleMerge` b))
    it "simpleMerge: cons is merged" $
      property (\(a::PSequent Int) (b::PSequent Int) -> Sequent.cons a ++ Sequent.cons b == Sequent.cons (a `Sequent.simpleMerge` b))
    it "greedy approach works for classical logic" $
      property (\(a::PSequent Int) -> isJust (Sequent.prove a) == Sequent.verifyTree (Sequent.greedyTree a))
  describe "ZipperSequent" $ do
    it "zipper2simple inverse of simple2zipper:" $
      property (\(s::PSequent Int) -> (Sequent.zipper2simple . Sequent.simple2zipper) s == s)
  describe "Intuisionistic logic" $ do
    it "Intuisionistic truth implies classical truth" $
      property (\(s::Sequent.SimpleSequent (InForm Int)) -> isJust (Sequent.prove s) <= isJust (Sequent.prove $ inseq2clas s))
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
    it "SequentTree gets exported properly" $
      toLatex proofTree `shouldBe` proofTreeTex


\end{code}

To run the tests, use \verb|stack test|.

\ignore{
\begin{code}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}

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
    ( simpleSeq,
      zipSeq,
      )
import PropSeq
import InSeq
import ModalSeq
import Latex

import Data.List

import Test.Hspec
import Test.QuickCheck
import Data.Maybe (isJust, isNothing)
\end{code}
}
\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

In order to make it more likely that our code works correctly we have
implemented a test suite. First we have written a list of formula that either
should or should not be valid in classical/intuitionistic/modal logic.

\begin{code}
p, q, r :: PropForm Int
(p, q, r) = (P 1, P 2, P 3)

fromForms :: Sequent s => [f] -> [s f]
fromForms = map (fromCons . return)

validIForms :: [InForm Int]
validIForms = In <$> [
    p --> p,
    Neg (p & Neg p),
    Top,
    ((p --> q) & (q --> r)) --> (p --> r)
  ]

validISequents :: [ISequent Int]
validISequents = (inSeq <$> [
    S [p `Disj` q] [p, q],
    S [p, q] [p & q],
    S [p, q] [p, q]
  ]) ++ fromForms validIForms

validForms :: [PropForm Int]
validForms =
  [
    p `Disj` Neg p,
    Neg (Neg p) --> p
  ]

validSequents :: [PSequent Int]
validSequents = [
    S [Neg (Neg p)] [p],
    S [] [p, Neg p]
  ] ++ (clasSeq <$> validISequents) ++ fromForms validForms

invalidForms :: [PropForm Int]
invalidForms = [
    p,
    p & q,
    p --> Neg p,
    Bot
  ]

invalidSequents :: [PSequent Int]
invalidSequents = [
    S [] [p, q],
    S [p `Disj` q] [p]
  ] ++ fromForms invalidForms

invalidIForms :: [InForm Int]
invalidIForms = In <$> [
    p `Disj` Neg p,
    Neg (Neg p) --> p
  ]

invalidISequents :: [ISequent Int]
invalidISequents = (inSeq <$> [
    S [Neg (Neg p)] [p],
    S [] [p, Neg p]
  ]) ++ (inSeq <$> invalidSequents) ++ fromForms invalidIForms

validMSequents :: [MSequent Int]
validMSequents =  [
    S [Dia (Prop (p `Disj` q))] [Dia (Prop p), Dia (Prop q)],
    S [Dia (Prop (p `Impl` q)), Box (Prop p)] [Dia (Prop q)],
    S [(Box . Dia . Box . Dia) (Prop p)] [(Box . Dia ) (Prop p)],
    S [(Box . Dia . Box) (Prop p), (Box . Dia . Box) (Prop q)] [(Box . Dia . Box) (Prop (p `Conj` q))]
  ] ++ (modSeq <$> validSequents)

invalidMSequents :: [MSequent Int]
invalidMSequents = S [(Dia . Box) (Prop p), (Dia . Box) (Prop q)] [Prop (p `Conj` q)]
  : (modSeq <$> invalidSequents)
\end{code}

To test the \LaTeX{} generation code, we have written what the corresponding
LaTeX code is supposed to be.
\begin{code}
validFormsTex :: [String]
validFormsTex =
  [
    "p_{1}\\vee \\neg p_{1}",
    "\\neg \\neg p_{1}\\to p_{1}"
  ]

validSequentsTex :: [String]
validSequentsTex =
  [
    "\\neg \\neg p_{1}\\Rightarrow p_{1}",
    "\\Rightarrow p_{1},\\neg p_{1}",
    "p_{1}\\vee p_{2}\\Rightarrow p_{1},p_{2}",
    "p_{1},p_{2}\\Rightarrow p_{1}\\wedge p_{2}",
    "p_{1},p_{2}\\Rightarrow p_{1},p_{2}",
    "\\Rightarrow p_{1}\\to p_{1}",
    "\\Rightarrow \\neg (p_{1}\\wedge \\neg p_{1})",
    "\\Rightarrow \\top ",
    "\\Rightarrow (p_{1}\\to p_{2})\\wedge (p_{2}\\to p_{3})\\to (p_{1}\\to p_{3})",
    "\\Rightarrow p_{1}\\vee \\neg p_{1}",
    "\\Rightarrow \\neg \\neg p_{1}\\to p_{1}"
  ]
\end{code}
We also have written the LaTeX code of a proof tree.
\begin{code}
proofTree :: SequentTree SimpleSequent (PropForm Int) PropRule
proofTree = Application PropSeq.ImplR (S [P 1] [Impl (P (0 :: Int)) (Impl (Conj (P 1) (Neg (P 0))) (P 1))]) [Application PropSeq.ImplR (S [P 1, P 0] [Impl (Conj (P 1) (Neg (P 0))) (P 1)]) [Application PropSeq.ConL (S [P 1, P 0, Conj (P 1) (Neg (P 0))] [P 1]) [Application PropSeq.NegL (Sequent.S [P 1, P 0, P 1, Neg (P 0)] [P 1]) [Axiom (S [P 1, P 0, P 1] [P 1, P 0])]]]]

proofTreeTex :: String
proofTreeTex = "\\begin{prooftree}\n\\hypo{p_{1},p_{0},p_{1}\\Rightarrow p_{1},p_{0}}\n\\infer1[\\(\\neg L\\)]{p_{1},p_{0},p_{1},\\neg p_{0}\\Rightarrow p_{1}}\n\n\\infer1[\\(\\wedge L\\)]{p_{1},p_{0},p_{1}\\wedge \\neg p_{0}\\Rightarrow p_{1}}\n\n\\infer1[\\(\\to R\\)]{p_{1},p_{0}\\Rightarrow p_{1}\\wedge \\neg p_{0}\\to p_{1}}\n\n\\infer1[\\(\\to R\\)]{p_{1}\\Rightarrow p_{0}\\to (p_{1}\\wedge \\neg p_{0}\\to p_{1})}\n\n\\end{prooftree}"
\end{code}
Here we add some aliases with stricter typing used as type hints in the tests.
\begin{code}
fromCons' :: [f] -> SimpleSequent f
fromCons' = fromCons

fromAnte' :: [f] -> SimpleSequent f
fromAnte' = fromAnte
\end{code}
Then finally, here we have our test specification.
\begin{code}
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
      all (Sequent.verifyTree . Sequent.greedyTree) validSequents `shouldBe` True
    it "invalid sequents are invalid" $
      any (Sequent.verifyTree . Sequent.greedyTree) invalidSequents `shouldBe` False
    it "seqTree: leafs cannot be simplified" $
      property (\(st::PSeqTree Int) -> all (\x -> null (expand x) || verifyAxiom x) $ leafs st)
    it "simpleMerge: ante is merged" $
      property (\(a::PSequent Int) (b::PSequent Int) -> Sequent.ante a ++ Sequent.ante b == Sequent.ante (a `Sequent.simpleMerge` b))
    it "simpleMerge: cons is merged" $
      property (\(a::PSequent Int) (b::PSequent Int) -> Sequent.cons a ++ Sequent.cons b == Sequent.cons (a `Sequent.simpleMerge` b))
    it "greedy approach works for classical logic" $
      property (\(a::PSequent Int) -> isJust (Sequent.prove a) == Sequent.verifyTree (Sequent.greedyTree a))
  describe "ZipperSequent" $ do
    it "simpleSeq inverse of zipSeq:" $
      property (\(s::PSequent Int) -> (simpleSeq . zipSeq) s == s)
    it "valid sequents are valid" $
      all (Sequent.verifyTree . Sequent.greedyTree) (zipSeq <$> validSequents) `shouldBe` True
    it "invalid sequents are invalid" $
      any (Sequent.verifyTree . Sequent.greedyTree) (zipSeq <$> invalidSequents) `shouldBe` False
  describe "Properties of intuitionistic logic" $ do
    it "Intuitionistic truth implies classical truth" $
      property (\(s::SimpleSequent (InForm Int)) -> isJust (prove s) <= isJust (prove $ clasSeq s))
    it "valid sequents are valid" $
      all (isJust . prove) validISequents `shouldBe` True
    it "invalid sequents are invalid" $
      any (isJust . prove) invalidISequents `shouldBe` False
  describe "Properties of modal logic" $ do
    it "Modal truth equals classical truth for classical formulae" $
      property (\(s::SimpleSequent (PropForm Int)) -> isJust (prove s) == isJust (prove $ modSeq s))
    it "valid sequents are valid" $
      all (isJust . prove) validMSequents `shouldBe` True
    it "invalid sequents are invalid" $
      any (isJust . prove) invalidMSequents `shouldBe` False

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
      toLatex <$> validSequents `shouldBe` validSequentsTex
    it "Intuitionistic formulas are formatted the same as normal ones" $
      property (\(x::PropForm Int) -> toLatex (In x) == toLatex x)
    it "Intuitionistic sequent trees are formatted the same as normal ones" $
      property (\(x::PSequent Int) -> toLatex (inSeq x) == toLatex x)
    it "SequentTree gets exported properly" $
      toLatex proofTree `shouldBe` proofTreeTex
\end{code}

To run the tests, use \verb|stack test|.

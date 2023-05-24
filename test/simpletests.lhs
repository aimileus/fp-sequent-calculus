
\section{Simple Tests}
\label{sec:simpletests}

We now use the library QuickCheck to randomly generate input for our functions
and test some properties.

\begin{code}
module Main where

import Sequent
import PropSeq

import Test.Hspec
import Test.QuickCheck
\end{code}

The following uses the HSpec library to define different tests.
Note that the first test is a specific test with fixed inputs.
The second and third test use QuickCheck.

\begin{code}
form1 :: PropForm Int
form1 = P 1 `Disj` (Neg (P 1))

s1 :: Sequent (PropForm Int)
s1 = fromCons form1

s1Tree :: SequentTree (PropForm Int) PropRule
s1Tree = prove s1

main :: IO ()
main = hspec $ do
  describe "Basics" $ do
    it "somenumbers should be the same as [1..10]" $
      somenumbers `shouldBe` [1..10]
    it "funnyfunction: result is within [1..100]" $
      property (\n -> funnyfunction n `elem` [1..100])
    it "myreverse: using it twice gives back the same list" $
      property $ \str -> myreverse (myreverse str) == (str::String)
\end{code}

To run the tests, use \verb|stack test|.

To also find out which part of your program is actually used for these tests,
run \verb|stack clean && stack test --coverage|. Then look for ``The coverage
report for ... is available at ... .html'' and open this file in your browser.
See also: \url{https://wiki.haskell.org/Haskell_program_coverage}.

\begin{code}
module Latex where

class ToLatex a where
  toLatex :: a -> String

instance ToLatex Int where
  toLatex :: Int -> String
  toLatex = show
\end{code}

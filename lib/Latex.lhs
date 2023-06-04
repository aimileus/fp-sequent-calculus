\ignore{
\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Latex where
\end{code}
}
\section{\LaTeX{} generation}

The latex generation is all done with a very simple typeclass. It contains just
a single function with a generic argument returning a string: the \LaTeX{} code.
The result of this function should return valid \LaTeX{} which when pasted into
a \emph{math mode} section should compile.
\begin{code}
class ToLatex a where
  toLatex :: a -> String

instance ToLatex Int where
  toLatex :: Int -> String
  toLatex = show
\end{code}

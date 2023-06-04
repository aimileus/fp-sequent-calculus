\ignore{
\begin{code}
{-# LANGUAGE InstanceSigs #-}

module Latex where

\end{code}
}
\section{\LaTeX{} generation}

The \LaTeX{} generation is all done with a very simple typeclass. It contains just
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
As it is possible that a prove function may fail, a prove function may return
something of type Maybe. For convenience in interactive use, implement a \LaTeX{}
generator for the Maybe type.
\begin{code}
instance (ToLatex a) => ToLatex (Maybe a) where
  toLatex :: Maybe a -> String
  toLatex Nothing = ""
  toLatex (Just a) = toLatex a
\end{code}
Finally add another convenience function to directly print \LaTeX{} to the console.
\begin{code}
printLatex :: ToLatex a => a -> IO ()
printLatex = putStrLn . toLatex
\end{code}

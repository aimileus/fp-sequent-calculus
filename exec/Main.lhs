
\section{Wrapping it up in an exectuable}
\label{sec:Main}

We will now use the library form Section \ref{sec:Sequent} in a program.

\begin{code}
module Main where

main :: IO ()
main = print "Hello World"
\end{code}

The output of the program is something like this:

\begin{showCode}
Hello!
[1,2,3,4,5,6,7,8,9,10]
[100,100,300,300,500,500,700,700,900,900]
[1,3,0,1,1,2,8,0,6,4]
[100,300,42,100,100,100,700,42,500,300]
GoodBye
\end{showCode}

Note that the above \texttt{showCode} block is only shown, but it gets
ignored by the Haskell compiler.

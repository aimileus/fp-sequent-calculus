\ignore{
\begin{code}
module Utils where
\end{code}}

\appendix
\section{Utilities}
In this section we define some helper functions that are general outside sequent
calculus.

First we give a function that returns all possible list with one element removed,
combined with this element.
\begin{code}
holes :: [a] -> [([a], a)]
holes [] = []
holes (x : xs) = (xs, x) : fmap (mapFst (x :)) (holes xs)
\end{code}

Then we give some functions to map over the first or second element of the tuple
\begin{code}
mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = fmap
\end{code}

We also have a function to return the first just element from the list,
when it exists.
\begin{code}
firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs
\end{code}

Finally we give a function to compute the Carthesian product: every possible
combination from items in the list. The elements of type \texttt{[a]} in the list
of the return type can be viewed as tuples without a predetermined length.
\begin{code}
-- alternatively: combs = foldr ((<*>) . ((:) <$>)) [[]]
combs :: [[a]] -> [[a]]
combs = foldr merge [[]]
    where
        merge xs1 xs2 = (:) <$> xs1 <*> xs2
\end{code}

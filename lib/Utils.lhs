\appendix
\section{Utilities}
In this section we define some helper functions that are general outside sequent
calculus.
\begin{code}
module Utils where

holes :: [a] -> [([a], a)]
holes [] = []
holes (x : xs) = (xs, x) : fmap (mapFst (x :)) (holes xs)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = fmap

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just x : _) = Just x
firstJust (Nothing : xs) = firstJust xs

-- alternatively: combs = foldr ((<*>) . ((:) <$>)) [[]]
combs :: [[a]] -> [[a]]
combs = foldr merge [[]]
    where
        merge xs1 xs2 = (:) <$> xs1 <*> xs2

\end{code}

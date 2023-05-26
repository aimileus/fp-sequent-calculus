\begin{code}
module Utils where

holes :: [a] -> [([a], a)]
holes [] = []
holes (x : xs) = (xs, x) : fmap (mapFst (x :)) (holes xs)

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (x, y) = (f x, y)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd = fmap

\end{code}
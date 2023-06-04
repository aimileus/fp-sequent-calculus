\ignore{
\begin{code}
{-# LANGUAGE InstanceSigs #-}

module ZipperSequent where
import Sequent
import Data.Maybe ( maybeToList )
\end{code}}

\begin{code}
data Zipper a = Z [a] [a] deriving (Eq, Show)
data ZipperSequent f = ZS (Zipper f) (Zipper f) deriving (Eq, Show)

instance Functor Zipper where
    fmap f (Z a b) = Z (f <$> a) (f <$> b)

list2zipper :: [f] -> Zipper f
list2zipper xs = Z xs []

simple2zipper :: SimpleSequent f -> ZipperSequent f
simple2zipper (S xs ys) = ZS (list2zipper xs) (list2zipper ys)

zipper2list :: Zipper f -> [f]
zipper2list (Z xs ys) = xs ++ ys

zipper2simple :: ZipperSequent f -> SimpleSequent f
zipper2simple (ZS zx zy) = S (zipper2list zx) (zipper2list zy)

instance Functor ZipperSequent where
    fmap f (ZS zx zy) = ZS (f <$> zx) (f <$> zy)

instance Sequent ZipperSequent where
  ante :: ZipperSequent f -> [f]
  ante = ante . zipper2simple
  cons :: ZipperSequent f -> [f]
  cons = cons . zipper2simple
  fromAnte :: [f] -> ZipperSequent f
  fromAnte = simple2zipper . fromAnte
  fromCons :: [f] -> ZipperSequent f
  fromCons = simple2zipper . fromCons

  expand (ZS (Z [] _) (Z [] _)) = []
  expand (ZS (Z (x:xs) y) z) = maybeToList $ ZS (Z xs y) z `applyExpansion` expandLeft x
  expand (ZS x (Z (y:ys) z)) = maybeToList $ ZS x (Z ys z) `applyExpansion` expandRight y
\end{code}

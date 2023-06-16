\ignore{
\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module ZipperSequent where
import Sequent
import PropSeq
import Data.Maybe ( maybeToList )
\end{code}
}
\section{Zipper Sequent}
In this section we give an introduction to an alternative data structure to store
sequents. One possible problem with sequents is it is theoretically possible that
there are a lot of irrelevant formula in the sequent. These formula may be at the
beginning of the list. Therefore it would be necessary to traverse them every time,
even when they cannot be expanded any further. Therefore we can split the list into
two parts: firstly a list of formula that we still need to look at. Secondly a
list of atomic propositions, that need not be checked further. Although we do not
strictly use this as a zipper, this was inspired by the Zipper data structure, so we
call these ZipperSequent. First we implement a data structure called Zipper used to
store these two lists.

This ZipperSequent currently only supports classical propositional logic.

\begin{code}
data Zipper a = Z [a] [a] deriving (Eq, Show)

instance Functor Zipper where
  fmap f (Z a b) = Z (f <$> a) (f <$> b)

list2zipper :: [f] -> Zipper f
list2zipper xs = Z xs []

zipper2list :: Zipper f -> [f]
zipper2list (Z xs ys) = xs ++ ys

zipperMerge :: Zipper a -> Zipper a -> Zipper a
zipperMerge (Z x1 y1) (Z x2 y2) = Z (x1 ++ x2) (y1 ++ y2)
\end{code}

Then we can define a ZipperSequent based on the Zipper instead of the list.

\begin{code}
data ZipperSequent f = ZS (Zipper f) (Zipper f) deriving (Eq, Show)

zipSeq :: SimpleSequent f -> ZipperSequent f
zipSeq (S xs ys) = ZS (list2zipper xs) (list2zipper ys)

simpleSeq :: ZipperSequent f -> SimpleSequent f
simpleSeq (ZS zx zy) = S (zipper2list zx) (zipper2list zy)

instance Functor ZipperSequent where
  fmap f (ZS zx zy) = ZS (f <$> zx) (f <$> zy)
\end{code}

When we perform the expansion, we only look at the first element of the first list.
When this element is atomic, we need not expand it any further, and move it to the
second list. Otherwise, we apply this expansion. This greedy approach to applying
expansions only works for classical propositional logic. A bit more care would be
required for modal and intuitionistic formulae.
\begin{code}
isAtomicExp :: Expansion s f r -> Bool
isAtomicExp (Atomic _) = True
isAtomicExp _ = False

instance Sequent ZipperSequent where
  ante :: ZipperSequent f -> [f]
  ante = ante . simpleSeq
  cons :: ZipperSequent f -> [f]
  cons = cons . simpleSeq
  fromAnte :: [f] -> ZipperSequent f
  fromAnte = zipSeq . fromAnte
  fromCons :: [f] -> ZipperSequent f
  fromCons = zipSeq . fromCons

  expand (ZS (Z [] _) (Z [] _)) = []
  expand (ZS (Z (x:xs) y) z) = let e = expandLeft x in
    if isAtomicExp e then expand (ZS (Z xs (x:y)) z) else maybeToList $ ZS (Z xs y) z `applyExpansion` e
  expand (ZS x (Z (y:ys) z)) = let e = expandRight y in
    if isAtomicExp e then expand (ZS x (Z ys (y:z))) else maybeToList $ ZS x (Z ys z) `applyExpansion` e
\end{code}

Then we can straightforwardly convert types to implement the Expandable type class. Note that
we flip the arguments to \texttt{zipperMerge}. The first argument to the merge function is the
base sequent, which is likely the biggest sequent. Therefore, we want to put this part at the end
to speed up the concatination.

\begin{code}
toZipperExpand :: (PropForm f -> Expansion SimpleSequent (PropForm f) r) -> PropForm f -> Expansion ZipperSequent (PropForm f) r
toZipperExpand e f = convert (e f)
  where
    convert (Exp _ s r) = Exp zipperSeqMerge (zipSeq <$> s) r
    convert (Atomic f') = Atomic f'

    zipperSeqMerge :: ZipperSequent f -> ZipperSequent f -> ZipperSequent f
    zipperSeqMerge (ZS x1 y1) (ZS x2 y2) = ZS (zipperMerge x2 x1) (zipperMerge y2 y1)

instance Eq p => Expandable ZipperSequent (PropForm p) PropRule where
  expandLeft = toZipperExpand expandLeft
  expandRight = toZipperExpand expandRight
\end{code}

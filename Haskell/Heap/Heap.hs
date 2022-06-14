-- Heap.hs
-- Bartlomiej Krolikowski

module Heap
( Heap()
, emptyHeap
, size
, insert
, extractMax
, getMax
, fromList
, toList
) where

data Heap n a = Null | Node { element :: a, left :: Heap n a, leftSize :: n, right :: Heap n a, rightSize :: n } deriving Show

emptyHeap :: Heap n a
emptyHeap = Null

size :: (Num n) => Heap n a -> n
size Null = 0
size h = leftSize h + rightSize h + 1

insert :: (Ord n, Num n, Ord a) => a -> Heap n a -> Heap n a
insert a Null = Node a Null 0 Null 0
insert a (Node a' l ls r rs)
    | ls > rs   = Node greater l ls (insert lower r) (rs+1)
    | otherwise = Node greater (insert lower l) (ls+1) r rs
    where lower = min a a'
          greater = max a a'

extractMax :: (Ord n, Num n, Ord a) => Heap n a -> (Maybe a, Heap n a)
extractMax Null = (Nothing, Null)
extractMax h =
    let Just (leaf, heap) = extractLastLeaf h
    in  (Just $ element h, heapify $ swapTop leaf heap)

getMax :: Heap n a -> Maybe a
getMax Null = Nothing
getMax heap = Just $ element heap

fromList :: (Ord n, Num n, Ord a) => [a] -> Heap n a
fromList = foldl (flip insert) emptyHeap

toList :: (Ord n, Num n, Ord a) => Heap n a -> [a]
toList Null = []
toList heap =
    let (Just a, heap') = extractMax heap
    in  a:toList heap'

extractLastLeaf :: (Ord n, Num n) => Heap n a -> Maybe (a, Heap n a)
extractLastLeaf Null = Nothing
extractLastLeaf (Node a Null _ Null _) = Just (a, Null)
extractLastLeaf (Node a l ls r rs)
    | ls > rs   = (\ (a', newL) -> (a', Node a newL (ls-1) r rs)) <$> extractLastLeaf l
    | otherwise = (\ (a', newR) -> (a', Node a l ls newR (rs-1))) <$> extractLastLeaf r

heapify :: (Num n, Ord a) => Heap n a -> Heap n a
heapify Null = Null
heapify all@(Node _ Null _ Null _) = all
heapify all@(Node a l ls Null rs)
    | a < element l = Node (element l) (heapify $ swapTop a l) ls Null rs
    | otherwise     = all
heapify all@(Node a Null ls r rs)
    | a < element r = Node (element r) Null ls (heapify $ swapTop a r) rs
    | otherwise     = all
heapify all@(Node a l ls r rs)
    | element l <= element r && a < element r = Node (element r) l ls (heapify $ swapTop a r) rs
    | element r <= element l && a < element l = Node (element l) (heapify $ swapTop a l) ls r rs
    | otherwise = all

swapTop :: a -> Heap n a -> Heap n a
swapTop _ Null = Null
swapTop newA (Node a l ls r rs) = Node newA l ls r rs

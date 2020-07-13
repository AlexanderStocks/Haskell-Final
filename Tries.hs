module Tries where

import Data.List hiding (insert)
import Data.Bits

import Types
import HashFunctions
import Examples

--------------------------------------------------------------------
-- Part I

-- Use this if you're counting the number of 1s in every
-- four-bit block...
bitTable :: [Int]
bitTable
  = [0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

countOnes :: Int -> Int
countOnes n
  | n < 2     = n
  | otherwise = second + countOnes first
    where
      (first, second) = quotRem n 2

countOnesFrom :: Int -> Int -> Int
countOnesFrom i n
  = countOnes (n .&. (bit i - 1))

getIndex :: Int -> Int -> Int -> Int
getIndex num block bSize
  = shiftR (num .&. (bit ((block + 1) * bSize) - 1)) (block * bSize)


-- Pre: the index is less than the length of the list
replace :: Int -> [a] -> a -> [a]
replace num (x:xs) rep
  | num == 0  = rep : xs
  | otherwise = x : replace (num - 1) xs rep

-- Pre: the index is less than or equal to the length of the list
insertAt :: Int -> a -> [a] -> [a]
insertAt num item []
  = [item]
insertAt num item list@(x:xs)
  | num == 0  = item : list
  | otherwise = x : insertAt (num - 1) item xs


--------------------------------------------------------------------
-- Part II

sumTrie :: (Int -> Int) -> ([Int] -> Int) -> Trie -> Int
sumTrie f1 f2 (Leaf ints)
  = f2 ints
sumTrie f1 f2 (Node a elems)
  = sum (map (sumTrie' f1 f2) elems)

sumTrie' :: (Int -> Int) -> ([Int] -> Int) -> SubNode -> Int
sumTrie' f1 f2 (Term num)
  = f1 num
sumTrie' f1 f2 (SubTrie trie)
  = sumTrie f1 f2 trie

trieSize :: Trie -> Int
trieSize t
  = sumTrie (const 1) length t

binCount :: Trie -> Int
binCount t
  = sumTrie (const 1) (const 1) t

meanBinSize :: Trie -> Double
meanBinSize t
  = fromIntegral (trieSize t) / fromIntegral (binCount t)


member :: Int -> Hash -> Trie -> Int -> Bool
member value hash trie bSize
  = member' trie 0
  where
    member' :: Trie -> Int -> Bool
    member' (Node bitVector subnodes) level
      | testBit bitVector i = member'' (subnodes !! onesRight) level
      | otherwise           = False
        where
          i         = getIndex hash level bSize
          onesRight = countOnesFrom bitVector i
          member'' :: SubNode -> Int -> Bool
          member'' (Term a) level'
            = a == value
          member'' (SubTrie trie) level'
            = member' trie (level' + 1)

--------------------------------------------------------------------
-- Part III
--my nodes are in the opposite order to the tests but the notes say thats fine
insert :: HashFun -> Int -> Int -> Int -> Trie -> Trie
insert hFun maxDepth bSize value trie
  = insert' value 0 trie
    where
      insert' :: Int -> Int -> Trie -> Trie
      insert' value' level (Leaf ints)
        | level == maxDepth - 1 = Leaf [value']
        | elem value' ints      = Leaf ints
        | otherwise = Leaf (value' : ints)
      insert' value' level (Node bitVector subNodes)
        | level == maxDepth - 1 = Leaf [value']
        | testBit bitVector i   = (Node bitVector newSubNodes)
        | otherwise = Node newBitVector (insertAt i (Term value') subNodes)
        where
          newSubNodes  = replace i subNodes newSubNode
          newBitVector = setBit bitVector i
          i            = getIndex (hFun value') level bSize
          newSubNode   = replace' (subNodes !! i)
          replace' :: SubNode -> SubNode
          replace' (Term v')
            | value' == v' = (Term v')
            | otherwise    = SubTrie (insert' (hFun value') (level + 1) (shortInsert (hFun v') empty))
              where
                shortInsert = insert hFun maxDepth bSize
          replace' (SubTrie trie')
            = SubTrie (insert' value' (level + 1) trie')


buildTrie :: HashFun -> Int -> Int -> [Int] -> Trie
buildTrie hFun maxDepth bSize ints
  = foldr (insert hFun maxDepth bSize) empty ints

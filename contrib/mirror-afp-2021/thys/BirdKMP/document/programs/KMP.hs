module KMP where

-- For testing
import Data.List ( isInfixOf )
import qualified Test.QuickCheck as QC

-- Bird's Morris-Pratt string matcher, without the `K' optimisation
-- Chapter 17, "Pearls of Functional Algorithm Design", 2010.

data Tree a = Null
            | Node [a] (Tree a) {- ! -} (Tree a) -- remains correct with strict right subtrees

matches :: Eq a => [a] -> [a] -> [Integer]
matches ws = map fst . filter (ok . snd) . scanl step (0, root)
  where
    ok (Node vs _l _r) = null vs
    step (n, t) x = (n + 1, op t x)

    op Null _x = root
    op (Node [] l _r) x = op l x
    op (Node (v : _vs) l r) x = if x == v then r else op l x

    root = grep Null ws

    grep l [] = Node [] l Null
    grep l vvs@(v : vs) = Node vvs l (grep (op l v) vs)

-- matches [1,2,3,1,2] [1,2,1,2,3,1,2,3,1,2]

-- Our KMP (= MP with the `K` optimisation)

kmatches :: Eq a => [a] -> [a] -> [Integer]
kmatches ws = map fst . filter (ok . snd) . scanl step (0, root)
  where
    ok (Node vs _l _r) = null vs
    step (n, t) x = (n + 1, op t x)

    op Null _x = root
    op (Node [] l _r) x = op l x
    op (Node (v : _vs) l r) x = if x == v then r else op l x

    root = grep Null ws

    next _x Null = Null
    next _x t@(Node [] _l _r) = t
    next x t@(Node (v : _vs) l _r) = if x == v then l else t

    grep l [] = Node [] l Null
    grep l vvs@(v : vs) = Node vvs (next v l) (grep (op l v) vs)

prop_matches :: [Bool] -> [Bool] -> Bool
prop_matches as bs = (as `isInfixOf` bs) == (as `matches` bs /= [])

prop_kmatches :: [Bool] -> [Bool] -> Bool
prop_kmatches as bs = (as `matches` bs) == (as `kmatches` bs)

tests :: IO ()
tests =
  do QC.quickCheck prop_matches
     QC.quickCheck prop_kmatches

{-
A174094: Number of ways to choose n positive integers less than or equal
to 2n such that none of the n integers divides another.

Author: Bertram Felgenhauer <int-e@gmx.de>

We can decompose the set {1..2n} into n chains (w.r.t. divisibility)

  P_k = {(2k-1) * 2^i | i in N} intersection {1..2n}   (k = 1..n)

In order to find a solution, we need to pick a divisor of each of these
chains. (Whenever we pick an element of one of the chains, all other
elements of that chain are excluded from the solution. See also Dilworth's
theorem.) We construct a search tree for this problem.

Each node of the search tree is a list of candidate sets (the root node
uses the chains P_k as candidate sets), and a solution to such a subproblem
is a selection of one element of each of the candidate sets such that none
of these numbers divides another. There are a few basic operations on these
problems that give rise to search trees.

 * branch: if there is a candidate set containing n, either:
   a) drop the candidate set and remove all divisors and multiples of n
      from the remaining candidate sets
   b) remove n from the candidate set

 * backtrack: if a candidate set is empty, there can be no solution

 * split: if the candidate set list can be split into two parts whose
   unions do not clash (sets P and Q clash if there are x in P, y in Q
   such that x | y or y | x), then count solutions for each of the parts
   separately and multiply the results (the parts are independent).

By combining branch and backtrack, we get unit propagation: if a singleton
candidate set exists, we can select that candidate immediately (skipping
part b) of 'branch' because that would immediately result in a backtrack).

Strategy: We try to make 'split' applicable as soon as possible; in order
to achieve that, we 'branch' on the smallest available number. [In fact,
rather than branching on individual candidate sets and members, we pick
a number n and produce k+1 child nodes, where k is the number of candidate
sets that contain n. ('multibranch') However, since the candidate sets
are pairwise disjoint throughout the search, the multibranch degenerates
into a branch...]

After each '(multi)branch', we 'propagate' and 'backtrack' exhaustively;
on the resulting nodes, we apply 'split', and then solve the resulting
subproblems.

In fact we 'multipropagate', selecting the candidates from all singleton
candidate sets simultaneously.

History:

2018-02-22: Initial version.
2019-04-12: Use chains as candidate sets, which is /far/ more efficient
    than using the sets of divisors of the numbers n+1..2n.
-}

import qualified Data.IntSet as S
import Data.List
import System.IO

count :: Int -> Integer
count n = count ip
  where
    -- auxiliary: compute relevent divisors and multiples of a given number
    divs z = S.fromList [d | d <- [1..z], z `mod` d == 0]
    mults z = S.fromList [z*m | m <- [1..2*n `div` z]]

    -- Compute initial candidate sets, namely the chains
    -- {k*2^i | k odd, i <= log_2 (2n/k)}
    ip = [S.fromList (takeWhile (<= 2*n) (iterate (2*) k)) | k <- [1,3..2*n]]

    -- `count` is responsible for multi-branching
    count :: [S.IntSet] -> Integer
    count [] = 1
    count [s] = fromIntegral (S.size s)
    count p =
        -- sum [count' (us'' ++ vs') | us'' <- drop1 us'] +
        -- NOTE: in this incarnation of the code, us' is always a singleton
        -- list, because the initial candidate sets are pairwise disjoint.
        -- So the above sum is equal to just `count' vs'`.
        count' vs' +
        count' (map (S.delete bv) p)
      where
        -- branch on smallest remaining number ('multibranch')
        bv = minimum [x | Just (x, _) <- map S.minView p]

        -- compute clashing elements
        clash = divs bv `S.union` mults bv

        -- split candidate sets into those that contain bv and others
        -- (us, vs) = partition (bv `S.member`) p
        vs = filter (not . (bv `S.member`)) p
        -- us' = map (`S.difference` clash) us
        vs' = map (`S.difference` clash) vs

    -- count' is responsible for multipropagation and splitting into
    -- independent subproblems
    count' :: [S.IntSet] -> Integer
    count' [] = 1
    count' [s] =
        -- shortcut if only a single candidate set is left:
        -- we have one solution for each element of s
        fromIntegral (S.size s)
    count' p
        | not (null os) =
            if -- check that there are no duplicate choices or empty sets
               -- among the elements of `os`
               S.size bvs /= length os ||
               -- check whether any of the choices clash with each other
               or [y `mod` x == 0
                  -- x `mod` y == 0 is impossible because x < y
                  | x : xss <- tails (S.toAscList bvs), y <- xss]
            then 0
            else count' (map (`S.difference` clash) qs)
        | otherwise = product (map count (split p))
      where
        -- find forced conclusions ('multipropagate')
        (os, qs) = partition ((1 >=) . S.size) p

        -- find branch values (flatten os)
        bvs = S.unions os

        -- find clashing elements
        clash = S.unions [divs o `S.union` mults o | o <- S.toList bvs]

        -- find independent subproblems ('split')
        split [] = [[]]
        split (p : ps) = (p : concat qs) : rs
          where
            -- find all the potentially clashing elements for P:
            -- - if x in P is selected, then it will clash with any multiple
            --   or divisor of x
            p' = S.unions [divs x `S.union` mults x | x <- S.toList p]

            -- identify the partitions in `split ps` that clash with P
            (qs, rs) = partition (any (not . S.null . (`S.intersection` p')))
                (split ps)

-- drop1 returns all sublists of a given list with exactly one element removed
-- e.g. drop1 [1,2,3] = [[2,3],[1,3],[1,2]]
drop1 :: [a] -> [[a]]
drop1 [] = []
drop1 (x:xs) = xs : map (x:) (drop1 xs)

main = do
    -- interact nicely with output redirection
    hSetBuffering stdout LineBuffering
    -- compute sequence
    mapM_ (\(a, b) -> putStrLn $ unwords [show a, show b]) $
        [(n, count n) | n <- [1..]]

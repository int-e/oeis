{-
A174094: Number of ways to choose n positive integers less than or equal
to 2n such that none of the n integers divides another.

In order to find a solution, we need to pick a divisor of each of the
numbers n+1..2*n. Each node of the search tree is a list of candidate sets,
and a solution to such a subproblem is a selection of one element of each
of the candidate sets such that none of these numbers divides another.
There are a few basic operations on these problems that give rise to
search trees.

 * branch: if there is a candidate set containing n, either:
   a) drop the candidate set and remove all divisors and multiples of n
      from the remaining candidate sets
   b) remove n from the candidate set
 * backtrack: if a candidate set is empty, there can be no solution
 * split: if the candidate set list can be split into two parts whose
   unions are disjoint, then count solutions for each of the parts
   and multiply them (the parts are independent).

By combining branch and backtrack, we get unit propagation: if a singleton
candidate set exists, we can select that candidate immediately (skipping
part b) of 'branch' because that would immediately result in a backtrack).

Strategy: We try to make 'split' applicable as soon as possible; in order
to achieve that, we 'branch' on the smallest available number. In fact,
rather than branching on individual candidate sets and members, we pick
a number n and produce k+1 child nodes, where k is the number of candidate
sets that contain n. ('multibranch')

After each 'multibranch', we 'propagate' and 'backtrack' exhaustively;
on the remaining nodes, we apply 'split', and then solve the resulting
subproblems.

In fact we 'multipropagate', selecting the candidates from all singleton
candidate sets simultaneously.
-}

import qualified Data.IntSet as S
import Data.List

count :: Int -> Integer
count n = solve p0 where
    divs z = S.fromList [d | d <- [1..z], z `mod` d == 0]
    mults z = S.fromList [z*m | m <- [1..2*n `div` z]]

    -- setup: divisors of each of the numbers n+1..2*n
    p0 = [divs z | z <- [n+1..2*n]]

    solve :: [S.IntSet] -> Integer
    solve [] = 1
    solve [s] = fromIntegral (S.size s)
    solve p = sum [solve' (us'' ++ vs') | us'' <- drop1 us'] +
        solve' (map (S.delete pv) p)
      where
        -- branch on smallest remaining number ('multibranch')
        pv = minimum [x | Just (x, _) <- map S.minView p]
        pvs = divs pv `S.union` mults pv
        (us, vs) = partition (pv `S.member`) p
        us' = map (`S.difference` pvs) us
        vs' = map (`S.difference` pvs) vs

    solve' :: [S.IntSet] -> Integer
    solve' [] = 1
    solve' [s] = fromIntegral (S.size s)
    solve' p
        | not (null os) = if S.size oss /= length os then 0
                          else solve' (map (`S.difference` sos) qs)
        | otherwise = product (map solve (collect p))
      where
        -- find forced conclusions ('multipropagate')
        (os, qs) = partition ((1 >=) . S.size) p
        oss = S.unions os
        sos = S.unions [divs o `S.union` mults o | o <- S.toList oss]

        -- find independent subproblems ('split')
        collect [] = [[]]
        collect (p:ps) = (p : concat qs) : rs where
            (qs, rs) = partition (any (not . S.null . (`S.intersection` p)))
                (collect ps)

drop1 :: [a] -> [[a]]
drop1 [] = []
drop1 (x:xs) = xs : map (x:) (drop1 xs)

main = do
    mapM_ (\(a, b) -> putStrLn $ unwords [show a, show b]) $
        [(n, count n) | n <- [1..200]]

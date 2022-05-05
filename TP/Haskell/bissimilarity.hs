{-# LANGUAGE BangPatterns #-}

import qualified Data.Map as M
import qualified Data.Maybe as May
import qualified Data.Set as S
import Data.List (nub)


type State = Integer
type Name = String

type LTS = M.Map State (S.Set (Name, State))

-- LTS da ficha 2, exercício 1.
lts :: LTS
lts = M.fromList [
    (1, S.fromList [("a", 2), ("a", 3)]),
    (2, S.fromList [("b", 1), ("a", 3)]),
    (3, S.fromList [("a", 3), ("b", 1)]),

    (4, S.fromList [("a", 5)]),
    (5, S.fromList [("a", 5), ("b", 6)]),
    (6, S.fromList [("a", 5)]),

    (7, S.fromList [("a", 8)]),
    (8, S.fromList [("a", 8), ("b", 7)]),

    (9, S.empty)
    ]

{-
Os dois LTS abaixo estão nos slides sobre LTS, no segmento
da bissimulação, página 21.
-}
lts2 :: LTS
lts2 = M.fromList [
    (1, S.fromList [("a", 2)]),

    (2, S.fromList [("c", 3), ("c", 4)])
    ]

lts3 :: LTS
lts3 = M.fromList [
    (5, S.fromList [("a", 6), ("a", 8)]),

    (6, S.fromList [("c", 7)]),
    (8, S.fromList [("c", 9)])
    ]

lts2' :: LTS
lts2' = M.fromList [
    (1, S.fromList [("a", 2)]),

    (2, S.fromList [("c", 3), ("b", 4)])
    ]

lts3' :: LTS
lts3' = M.fromList [
    (5, S.fromList [("a", 6), ("a", 8)]),

    (6, S.fromList [("c", 7)]),
    (8, S.fromList [("b", 9)])
    ]

{-
LTS da ficha 5, exercício 5.
Nenhum deles é bissimilar a algum dos outros.
-}

act1 :: LTS
act1 = M.fromList [
    (1, S.fromList [("a", 2)]),
    (2, S.fromList [("b", 3)]),
    (3, S.fromList [("a", 1), ("b", 3)])
    ]

act2 :: LTS
act2 = M.fromList [
    (1, S.fromList [("a", 2)]),
    (2, S.fromList [("b", 2), ("b", 3)]),
    (3, S.fromList [("a", 1)])
    ]

act3 :: LTS
act3 = M.fromList [
    (1, S.fromList [("a", 2)]),
    (2, S.fromList [("b", 3), ("b", 4)]),
    (3, S.fromList [("b", 4)]),
    (4, S.fromList [("b", 4), ("a", 1)])
    ]

-- Given an LTS, a state and a label, return the set of states in that LTS which are reachable from
-- that state, via the provided label label.
next :: LTS -> State -> Name -> S.Set State
next lts s n = May.fromMaybe S.empty $ do
    labelsToStateSet <- M.lookup s lts
    return $ S.map snd $ S.filter (\(name, _) -> name == n) labelsToStateSet

-- Given an LTS and a state, return all the labels out of that state, in that LTS.
labelsFromState :: LTS -> State -> S.Set Name
labelsFromState lts s = May.fromMaybe S.empty $ do
    labelsToStateSet <- M.lookup s lts
    return $ S.map fst labelsToStateSet

-- Given two states and their respective LTS, return the set of
-- new possible relations with which to extend the bissimulation
-- being built.
-- The state/LTS used to "take the first step" are first ones provided,
-- and the second state/LTS argument will attempt to replicate the movements
-- taken in the first.
extendBissim :: LTS -> LTS -> State -> State -> S.Set (State, State)
extendBissim lts1 lts2 s t =
    let labelsFromS = labelsFromState lts1 s
        -- Implication as disjunction:
        -- there exist transitions labeled "lab" from state s => there must also exist "lab" transitions for t
        pred set1 set2 = null set1 || not (null set2)
    in if all (\lab -> pred (next lts1 s lab) (next lts2 t lab)) labelsFromS
            then S.fromList [(s', t') | lab <- S.toList labelsFromS
                                      , s' <- S.toList $ next lts1 s lab
                                      , t' <- S.toList $ next lts2 t lab]
            else mempty

bissimulation :: LTS -> LTS -> State -> State -> S.Set (State, State)
bissimulation l1 l2 p q = helper [(p,q)] (S.fromList [(p, q)])
    where
        helper [] set = set
        helper ((s, t) : rest) !set =
            let newPairs, newPairs' :: S.Set (State, State)
                newPairs = extendBissim l1 l2 s t
                -- Necessário inverter ordem dos pares que resultam desta alternativa.
                -- Ver exercício 1 da ficha 2 - quando se verificam alternativas de
                -- (a, b), e se deu o passo primeiro em b, os pares (a', b') podem
                -- ser considerados em qualquer ordem - (a', b'), (b', a'), mas a função de fecho
                -- transitivo abaixo tratará de calcular (b', a') por nós.
                newPairs' = S.map (\(a, b) -> (b, a)) $ extendBissim l2 l1 t s
                extension = newPairs `S.union` newPairs'
                set' = (set `S.union` extension)
                visitedAllFrom1 = S.map fst set' == S.fromList (M.keys act1)
                visitedAllFrom2 = S.map snd set' == S.fromList (M.keys act2)
            in case (null newPairs /= null newPairs', set' == set) of
                    (True, _) -> S.empty
                    (_, True) -> set'
                    (_, _)    -> helper (S.toList extension ++ rest) set'

transitiveClosure :: Ord a => S.Set (a, a) -> S.Set (a, a)
transitiveClosure closure = helper closure'
    where
        closureList = S.toList closure
        reflexive = S.fromList $ [(a, a) | (a, _) <- closureList]
        symmetric = S.fromList $ [(b, a) | (a, b) <- closureList]
        closure' = S.unions [closure, reflexive, symmetric]

        helper :: Ord a => S.Set (a, a) -> S.Set (a, a)
        helper set
            | set == closureUntilNow = set
            | otherwise              = transitiveClosure closureUntilNow
            where
                list = S.toList set
                closureUntilNow =
                    S.unions [
                        set,
                        S.fromList [(a, c) | (a, b) <- list, (b', c) <- list, b == b'],
                        S.fromList [(c, a) | (a, b) <- list, (b', c) <- list, b == b']
                    ]
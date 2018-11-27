{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.List
import Data.Bits
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import qualified Data.Map.Lazy as LM
import Text.Printf
import Numeric.LinearAlgebra hiding (find, (<>))
import Data.Functor
import Options.Applicative
import Control.Monad
import Data.Monoid
import Data.Function
import Debug.Trace

-- no warning about Debug.Trace please
_trace = trace

type Width = Int

type Mealy a b = [(a, ((a, [b]), (a, [b])))]

data L = S | M deriving (Eq, Ord, Enum, Bounded)

instance Show L where
    showsPrec _ S = ('S':)
    showsPrec _ M = ('M':)
    showList []   = ('·':)
    showList xs   = foldr ((.) . shows) id xs

buildMealyRTL :: Width -> Mealy Int L
buildMealyRTL 1 = [ (0, ((0, [S]), (0, [M]))) ]
buildMealyRTL w =
    [ (0, ((0, [S]), (1, [M]))) ] ++
    [ (i, ((j, [S]), (j, [S]))) | i <- [1..w-1] , let j = (i+1) `mod` w]

buildMealy :: Width -> Mealy Int L
buildMealy 1 = [ (0, ((0, [S]), (0,[M]))) ]
buildMealy w = [ (n, edges n) | n <- [0..2^(w-1)-1] ]
  where
    -- The root
    edges 0 = ( (0, [S]), (1, []) )
    -- The intermediate nodes (scanning until the end of the window)
    edges n | n < 2^(w-2) = ( (2*n, []), (2*n+1, []) )
    -- The last bit of the window, we can output the leak
    edges n = ( (0, output (2*n)), (0, output (2*n+1)) )

    output n = replicate (w - lastbit - 1) S ++ [M] ++ replicate lastbit S
      where Just lastbit = find (\i -> n `testBit` i) [0..]

-- | This function reduces the number of nodes by commoning up
-- equivalent nodes. Needs to be iterated.
reduceMealyOnce :: (Ord a, Ord b) => Mealy a b -> Mealy a b
reduceMealyOnce m
    = [ (n, ((f n0,s0), (f n1,s1)))
      | (n, ((n0,s0), (n1,s1))) <- m
      , f n == n
      ]
  where
    f = (M.!) $
        M.fromList
        [ (x, head dup)
        | dupSet <- M.elems $ M.fromListWith S.union [ (e,S.singleton n) | (n,e) <- m ]
        , let dup = S.toList dupSet
        , x <- dup
        ]

reduceMealy :: (Ord a, Ord b) => Mealy a b -> Mealy a b
reduceMealy m | length m == length m' = m
              | otherwise             = reduceMealy m'
  where m' = reduceMealyOnce m

mealy2dot :: (Show a, Show b) => Mealy a b -> String
mealy2dot nodes = unlines $
    [ "digraph {" ] ++
    [ printf "%s -> %s [label=\"0/%s\"];\n" (show n) (show n0) (show s0) ++
      printf "%s -> %s [label=\"1/%s\"];" (show n) (show n1) (show s1)
    | (n, ((n0, s0), (n1,s1))) <- nodes ] ++
    [ "}" ]


type Markov a = [(a, [a])]

buildMarkov :: (Ord a, Ord b) => (a,[b]) -> Mealy a b -> Markov (a,[b])
buildMarkov start mealy = go (S.singleton start) S.empty []
  where
    go todo done
        | S.null todo = id
        | (node,text) `S.member` done = go todo' done
        | otherwise = (((node,text), [n0', n1']):) .
            go todo'' (S.insert (node,text) done)

      where
      ((node,text), todo') = S.deleteFindMin todo
      Just ((n0, s0), (n1, s1)) = lookup node mealy
      n0' = (n0, tail text ++ s0)
      n1' = (n1, tail text ++ s1)
      todo'' = S.insert n0' (S.insert n1' todo')


markov2dot :: (a -> String) -> (a -> String) -> Markov a -> String
markov2dot col s nodes = unlines $
    [ "digraph {"
    -- , "layout = neato;"
    , "margin = 0;"
    , "epsilon = 0.0001;"
    , "splines=true;"
    -- , "edge [len = 0.8];"
    , "edge [len = 1.3];"
    , "node [width=0.2];"
    , "node [height=0.2];"
    , "node [style=filled];"
    ] ++
    [ printf "%s [ color=%s]" (s n) (col n)
    | (n, _) <- nodes ] ++
    [ printf "%s -> %s;\n" (s n) (s n')
    | (n, succs) <- nodes , n' <- succs] ++
    [ "}" ]

type Dist a = M.Map a Double

stationary :: Ord a => Markov a -> Dist a
stationary = stationaryCond (const True)

findMaxIndex f xs = snd (maximum (zip (map f xs) [0..]))

stationaryCond :: Ord a => (a -> Bool) -> Markov a -> Dist a
stationaryCond nonDead markov
    -- | not ok1 = error "First eigenvalue not 1"
    | not ok2 = error "Eigenvector does not consist of probabilities"
    -- | not ok3 = error "Eigenvector does not have eigenvalue 1"
    | otherwise = M.fromList $ zip (map fst markov) (toList evec)
  where
    n = length markov

    transMatrix :: Matrix Double
    transMatrix = (n >< n) $
        [ if nonDead n then sum [ p | n' <- e, n' == n0 ] else 0
        | (n,e) <- markov
        , (n0,_) <- markov
        , let p = 1/fromIntegral (length e)
        ]

    (evals, evecs) = eig (tr transMatrix)
    -- Just i = findIndex isOne (toList evals)
    i = findMaxIndex realPart (toList evals)
    eval = evals `atIndex` i
    evecC = toColumns evecs !! i
    evecNorm = scale (1/sum (toList evecC)) evecC
    evec = cmap realPart evecNorm

    isOne c = magnitude (c - 1) < 0.0000001
    isProb c = abs (imagPart c) < 0.0000001 && realPart c >= 0 && realPart c <= 1

    ok1 = magnitude (eval - 1) < 0.001
    ok2 = all isProb (toList evecNorm)
    ok3 = norm_2 (evec - (evec <# transMatrix)) < 0.001


prodMarkov :: Markov a -> Markov (a,a)
prodMarkov markov =
    [ ((n1,n2), (,) <$> e1 <*> e2)
    | (n1, e1) <- markov
    , (n2, e2) <- markov
    ]

filterMarkov :: (a -> Bool) -> Markov a -> Markov (Maybe a)
filterMarkov p markov =
    (Nothing, [Nothing]) : [ (Just n, map (justIf p) e) | (n, e) <- markov, p n ]

justIf p n = if p n then Just n else Nothing

-- Removes all edges from nodes where p does not hold, and all nodes
-- not reachable
deadEnd :: Ord a => (a -> Bool) -> a -> Markov a -> Markov a
deadEnd p start markov = go S.empty [start]
  where
    edges = (M.fromList markov M.!)
    go done [] = []
    go done (x:todo) | x `elem` done = go done todo
                     | otherwise = (x, e) : go (S.insert x done) todo'
      where e = edges x
            todo' | p x      = e ++ todo
                  | otherwise = todo

liveNodes :: Ord a => a -> Markov a -> S.Set a
liveNodes start markov = go (S.singleton start)
  where
    edges = (M.fromList markov M.!)
    go live | S.size live == S.size live' = live
            | otherwise                   = go live'
      where live' = live `S.union` S.fromList [ n | (n,e) <- markov, any (`S.member` live) e ]

-- | This function reduces the number of nodes by commoning up
-- equivalent nodes. Needs to be iterated.
reduceMarkovOnce :: (Ord a, Ord b) => (a -> b) -> Markov a -> Markov a
reduceMarkovOnce l m
    = [ (n, map f e) | (n, e) <- m, f n == n ]
  where
    f = (M.!) $
        M.fromList
        [ (x, head dup)
        | dupSet <- M.elems $ M.fromListWith S.union [ ((l n,sort e),S.singleton n) | (n,e) <- m ]
        , let dup = S.toList dupSet
        , x <- dup
        ]

reduceMarkov :: (Ord a, Ord b) => (a -> b) -> Markov a -> Markov a
reduceMarkov leak m | length m == length m' = m
                    | otherwise             = reduceMarkov leak m'
  where m' = reduceMarkovOnce leak m

-- If two independent copies of the markov chain, starting in the given
-- distribution are run n steps, what is the probability that the output is the
-- same?
sampleCollisions :: forall a b. (Ord a, Eq b) => Int -> (a -> b) -> Markov a -> Dist a -> Double
sampleCollisions n f markov dist =
    sum [ p * fromIntegral (countCollisions n n1 n2)
        | ((n1, n2),p) <- M.toList $ prodDist dist
        ] / 2^(2*n)
 where
    edges = (M.fromList markov M.!)

    -- From these two states on for further n steps, how many collisions?
    countCollisions :: Int -> a -> a -> Integer
    countCollisions 0 _ _ = 1
    countCollisions i n1 n2
        | f n1 == f n2 = sum [ countMemo (i-1) (n1', n2')
                             | n1' <- edges n1
                             , n2' <- edges n2
                             ]
        | otherwise = 0

    -- Yay, memoization!
    countMemo = curry (LM.fromList [ ((i,(n1,n2)), countCollisions i n1 n2) | i <- [0..n], n1 <- map fst markov, n2 <- map fst markov] M.!)


-- A typical output function
leak :: (a,[b]) -> b
leak (_,s) = head s


colorNode :: (a,[L]) -> String
colorNode s = if leak s == S then "lightblue" else "green1"

showNode :: (Show a, Show b) => (a,[b]) -> String
showNode (node,s) = show s ++ show node

showNode2 :: (Show a, Show b) => ((a,[b]),(a,[b])) -> String
showNode2 (n1,n2) = showNode n1 ++ "_" ++ showNode n2

calcPnl :: forall a b. (Ord a, Ord b) => Int -> (a -> b) -> Markov a -> Dist a -> Dist (a, [b])
calcPnl n f markov dist = jointDist dist $ \x1 -> normDist $ leakDist n x1
 where
    edges = (M.fromList markov M.!)

    -- Calculate the distribution of leaks
    -- (of the given length, starting in the given node)
    -- This is the performance hot spot in this program! (until I introduce memoization)
    leakDist :: Int -> a -> Dist [b]
    leakDist 0 _    = M.singleton [] 1
    leakDist i node = M.mapKeysMonotonic (f node :) $ addDists $
                      [ leakDistMemo (i-1) n' | n' <- edges node ]

    -- Yay, memoization!
    leakDistMemo = curry (LM.fromList [ ((i,node), leakDist i node) | i <- [0..n], node <- map fst markov ] M.!)

calcPl :: forall a b. (Ord a, Ord b) => Int -> (a -> b) -> Markov a -> Dist a -> Dist [b]
calcPl n f markov dist =
    addDists [ fmap (p*) (normDist $ leakDist n x1) | (x1, p) <- M.toList dist ]
 where
    edges = (M.fromList markov M.!)

    -- Calculate the distribution of leaks
    -- (of the given length, starting in the given node)
    -- This is the performance hot spot in this program! (until I introduce memoization)
    leakDist :: Int -> a -> Dist [b]
    leakDist 0 _    = M.singleton [] 1
    leakDist i node = M.mapKeysMonotonic (f node :) $ addDists $
                      [ leakDistMemo (i-1) n' | n' <- edges node ]

    -- Yay, memoization!
    leakDistMemo = curry (LM.fromList [ ((i,node), leakDist i node) | i <- [0..n], node <- map fst markov ] M.!)

condEntropyLB :: (Ord a, Ord b) => Dist (a, [b]) -> Dist (a, [b]) -> Double
condEntropyLB pnl pnlbar = sum
    [ pxy * logb (px/pxy)
    | ((xi,ys),pxy) <- M.toList pnl
    , let px = pnlbar M.! (xi, init ys)
    ]

condEntropyUB :: Ord b => Dist [b] -> Dist [b] -> Double
condEntropyUB pl plbar = sum
    [ pxy * logb (px/pxy)
    | (ys,pxy) <- M.toList pl
    , let px = plbar M.! init ys
    ]

markovStepProb :: Ord a => (a -> Bool) -> Markov a -> Dist a -> Double
markovStepProb p markov dist = sum
    [ pn * sum [ 1 | n' <- e, p n'] / fromIntegral (length e)
    | (n,pn) <- M.toList dist
    , let e = edges n
    ]
  where
    edges = (M.fromList markov M.!)


logb :: Double -> Double
logb = logBase 2

samplesToDist :: Ord a => [a] -> Dist a
samplesToDist xs = normDist $ M.fromListWith (+) [ (x,1) | x <- xs ]

-- | Take the union of two distributions (not normalised)
addDist :: Ord a => Dist a -> Dist a -> Dist a
addDist = M.unionWith (+)

addDists :: Ord a => [Dist a]-> Dist a
addDists = M.unionsWith (+)

mapDist :: Ord b => (a -> b) -> Dist a -> Dist b
mapDist = M.mapKeysWith (+)

normDist :: M.Map a Double -> M.Map a Double
normDist m = fmap (/sum m) m

jointDist :: (Ord a, Ord b) => Dist a -> (a -> Dist b) -> Dist (a,b)
jointDist d1 f = M.unionsWith (error "Not disjoint") $
        [ M.mapKeysMonotonic (a,) $ fmap (p_a*) (f a)
        | (a, p_a) <- M.toList d1
        ]

prodDist :: Ord a => Dist a -> Dist (a,a)
prodDist d = M.fromListWith (error "input wrong") $
    [ ((x,y), px * py) | (x,px) <- M.toList d, (y,py) <- M.toList d ]

samplePred :: (a -> Bool) -> Dist a -> Double
samplePred ok d = sum [ p | (x,p) <- M.toList d, ok x ]

conditionalDist :: Ord a => Dist (Maybe a) -> Dist a
conditionalDist d = normDist $ M.fromListWith (error "input wrong") $
    [ (n, p) | (Just n, p) <- M.toList d ]

data WhichGraph = RTL | LTR deriving Eq
data WhatToDo = PrintMealy
              | PrintMarkov
              | PrintCollMarkov
              | PrintEntropy
              | PrintTableRow
              | PrintColl
    deriving Eq

run :: Int -> Int -> WhichGraph -> WhatToDo -> IO ()
run w n which todo = do
    let my = case which of
            RTL -> reduceMealy $ buildMealyRTL w
            LTR -> reduceMealy $ buildMealy w
    let n0 = (0, replicate w S)
    let mv = buildMarkov n0 my
    let sd = stationary mv
    let singletonDist = M.singleton n0 1
    let ud = M.fromList mv $> ((1::Double) / fromIntegral (length mv))
    let pnl    = calcPnl n leak mv sd
    let pnlbar = calcPnl (n-1) leak mv sd
    let eLB = condEntropyLB pnl pnlbar
    let pl     = calcPl n leak mv sd
    let plbar  = calcPl (n-1) leak mv sd
    let eUB = condEntropyUB pl plbar

    let prodMv   = prodMarkov mv
    let thinProdMV = reduceMarkov (\(n1,n2) -> leak n1 == leak n2) prodMv
        -- ^ This is just to feed less data to the linear algrebra system
    let collSD   = stationaryCond (\(n1,n2) -> leak n1 == leak n2) thinProdMV
    let collP    = samplePred (\(n1,n2) -> leak n1 == leak n2) collSD
    let collRate = - logb collP

    let simCollP = sampleCollisions n leak mv sd -- singletonDist
    let simCollisions = simCollP^(2::Int) * 2^n
    let simCollRate = - (logb simCollP) / fromIntegral n

    case todo of
        PrintMealy      -> putStrLn (mealy2dot my)
        PrintMarkov     -> putStrLn (markov2dot colorNode showNode mv)
        PrintCollMarkov -> error "unimplemented" -- putStrLn (markov2dot showNode2 collidingMv)
        PrintTableRow   -> printf "%d\t%d\t%f\t%f\t%f\n" w n eLB eUB collRate
        PrintColl       -> error "unimplemented"  -- print collisions
        PrintEntropy    -> printf "w: %2d. n: %3d. %.4f ≤ H(Y) ≤ %.4f. coll rate: %.4f. sim coll rate: %.4f \n"
                                w n eLB eUB collRate simCollRate


main :: IO ()
main = join . execParser $
  info (helper <*> parser)
  (  fullDesc
  <> header "Entropy calculation"
  )
  where
    parser :: Parser (IO ())
    parser = run
      <$> option auto
         (  long "width"
         <> short 'w'
         <> metavar "WIDTH"
         <> help "Width of the window (typical 4 or 5)"
         <> value 4
         <> showDefault
         )
      <*> option auto
         (  long "n"
         <> short 'n'
         <> metavar "N"
         <> help "approximation"
         <> value 10
         <> showDefault
         )
      <*> choice
        [ flag' LTR (long "ltr" <> help "Analyse left-to-right")
        , flag' RTL (long "rtl" <> help "Analyse right-to-left")
        , pure LTR
        ]
      <*> choice
        [ flag' PrintMealy    (long "mealy"  <> help "Print Mealy graph in .dot format")
        , flag' PrintMarkov   (long "markov" <> help "Print Markov graph in .dot format")
        , flag' PrintCollMarkov   (long "colliding-markov" <> help "Print colliding Markov graph in .dot format")
        , flag' PrintTableRow (long "table"  <> help "Print a tsv table row")
        , flag' PrintColl     (long "coll"   <> help "Print collision probability tsv row")
        , pure PrintEntropy
        ]

choice :: Alternative f => [f a] -> f a
choice = foldr1 (<|>)

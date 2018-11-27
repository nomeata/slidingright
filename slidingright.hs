{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Math.NumberTheory.Primes.Testing
import Math.NumberTheory.Moduli
import Options.Applicative
import System.Random
import System.IO
import System.Exit
import Data.Bits
import Data.Function
import Data.List
import Data.Maybe
import Test.QuickCheck
import Debug.Trace
import Control.Monad
import Statistics.Sample
import Statistics.Quantile
import Control.Exception (evaluate)
import Data.Bifunctor
import GHC.Stack
import Text.Read
import Text.Printf
import Data.List.Split
import qualified Data.Vector as V
import qualified Data.Sequence as S
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Monoid

-- Some convenient names for some parameters
type BitLength = Int
type Width = Int

-- http://stackoverflow.com/a/13301611/946226
rndPrime :: BitLength -> Gen Integer
rndPrime 1 = error "Cannot create distinct p and q for 1 bit"
rndPrime bits = do
    x <- fmap (.|. 1) $ choose (2^(bits - 1), 2^bits - 1)
    if isPrime x then return x else rndPrime bits

data RSAParams = RSAParams { bits :: Int, p, q, n, e, dp, dq, kp, kq :: Integer } deriving Show

instance Arbitrary RSAParams where
    arbitrary = sized (\s -> genRSAParams (min 1024 (max s 2)))

genRSAParams :: BitLength -> Gen RSAParams
genRSAParams bits = do
    p <- rndPrime bits
    q <- rndPrime bits
    let n = p*q
        e = 65537
        mdp = invertMod e (p-1)
        mdq = invertMod e (q-1)
    case (mdp, mdq) of
        (Just dp, Just dq) -> do
            let kp = (e*dp-1) `div` (p-1)
                kq = (e*dq-1) `div` (q-1)
            return (RSAParams {..})
        _ -> genRSAParams bits -- retry

data Step = S | M deriving (Eq, Ord, Show) -- square or multiply
type Leak = V.Vector Step

leftToRight :: BitLength -> Width -> Integer -> Leak
leftToRight bits w s | w <= 0 = error "width must be positive"
leftToRight bits w s = V.fromList $ go (bits-1)
   where
    go i | i < 0         = []
    go i | s `testBit` i = replicate (slideLength-1) S ++ M : go (i - slideLength)
      where
        Just slideLength = find (\l -> s `testBit` (i-l+1)) $ [w,w-1..1]
    go i | otherwise     = S : go (i-1)

-- Bits learned
leftToRightGMPBits :: BitLength -> Width -> Integer -> Integer
leftToRightGMPBits bits w s | w <= 0 = error "width must be positive"
leftToRightGMPBits bits w s = go (bits -1) 0
   where
    go i !acc | i < 0         = acc
    go i !acc | s `testBit` i = go (i - slideLength) (acc + learned)
      where
        Just slideLength = find (\l -> s `testBit` (i-l+1)) $ [w,w-1..1]
        learned | slideLength == 1 = 1
                | otherwise        = 2
    go i ! acc | otherwise    =  go (i-1) (acc + 1)

rightToLeft :: BitLength -> Width -> Integer -> Leak
rightToLeft bits w s | w <= 0 = error "width must be positive"
rightToLeft bits w s = V.fromList $ go 0 []
   where
    go i acc | i == bits     = acc
    go i acc | s `testBit` i = go (i+slideLength) (replicate (slideLength-1) S ++ M : acc)
      where slideLength = min w (bits - i)
    go i acc | otherwise     = go (i+1) (S : acc)

-- Bits learned
rightToLeftBits :: BitLength -> Width -> Integer -> Integer
rightToLeftBits bits w s | w <= 0 = error "width must be positive"
rightToLeftBits bits w s = go 0 0
   where
    go i !acc | i == bits     = acc
    go i !acc | s `testBit` i = go (i+slideLength) (1+acc)
      where slideLength = min w (bits - i)
    go i !acc | otherwise     = go (i+1) (1+acc)


-- A datatype to track known bits
data BitMask = BM { unknownBits :: !Integer, knownBits :: !Integer }
    deriving Eq

showBitMask bits bm = map go [(bits-1),(bits-2)..0]
  where go i | not (bm `isKnownBit` i) = '_'
             | bm `getKnownBit` i      = '1'
             | otherwise               = '0'

instance Show BitMask where
    show bm = showBitMask bits bm
      where bits = head [i | i <- [0..], 2^i > knownBits bm && 2^i > unknownBits bm]


isKnownBit :: BitMask -> Int -> Bool
bm `isKnownBit` i = not (unknownBits bm `testBit` i)

getKnownBit :: BitMask -> Int -> Bool
bm `getKnownBit` i = knownBits bm `testBit` i

possibleBits :: BitMask -> Int -> [Bool]
possibleBits bm i
    | bm `isKnownBit` i = [bm `getKnownBit` i]
    | otherwise         = [False, True]

matches :: Integer -> BitMask -> Bool
matches p bm = (p .|. unknownBits bm) == (knownBits bm .|. unknownBits bm)

isKnown :: BitMask -> Maybe Integer
isKnown bm | unknownBits bm == 0 = Just (knownBits bm)
           | otherwise           = Nothing

writeBit :: Int -> Bool -> Integer -> Integer
writeBit i True  p = p `setBit` i
writeBit i False p = p `clearBit` i

writeKnownBit :: Int -> Bool -> BitMask -> BitMask
writeKnownBit i b bm = BM (unknownBits bm `clearBit` i) (writeBit i b (knownBits bm))

nothingKnown :: BitLength -> BitMask
nothingKnown bits = BM (2^bits-1) 0

anyOddNumber :: BitLength -> BitMask
anyOddNumber bits = writeKnownBit 0 True (nothingKnown bits)

fromKnownNumber :: Integer -> BitMask
fromKnownNumber i = BM 0 i

-- can be optimized, I guess
allMatching :: BitMask -> [Integer]
allMatching bm = map sum $ mapM go [(bits-1),(bits-2)..0]
  where go i | not (bm `isKnownBit` i) = [2^i,0]
             | bm `getKnownBit` i      = [2^i]
             | otherwise               = [0]
        bits = head [i | i <- [0..], 2^i > knownBits bm && 2^i > unknownBits bm]

maskFromMatching :: [Integer] -> BitMask
maskFromMatching (m:ms) = foldl' go (fromKnownNumber m) ms
  where
    go :: BitMask -> Integer -> BitMask
    go bm i = BM (unknownBits bm .|. disagree) (knownBits bm `clear` disagree)
      where disagree = (unknownBits bm .|. knownBits bm) `xor` (unknownBits bm .|. i)

x `clear` y = complement (complement x .|. y)

countKnownBits :: BitLength -> BitMask -> Int
countKnownBits bits bm = bits - popCount (unknownBits bm)

-- A breadth first search limiting the count by n
bfSearch :: Int -> a -> (a -> [a]) -> (a -> Bool) -> Maybe Int
bfSearch limit s0 next done = go 0 (S.singleton s0)
  where
    go n _ | n >= limit = Nothing
    go n todo = case S.viewl todo of
        S.EmptyL -> Nothing
        s S.:< todo' | done s    -> Just n
                     | otherwise -> go (n+1) (todo' S.>< S.fromList (next s))

dfSearch :: Int -> a -> (a -> [a]) -> (a -> Bool) -> Maybe Int
dfSearch limit s0 next done = go 0 [s0]
  where
    go n _ | n >= limit = Nothing
    go n [] = Nothing
    go n (s:todo') | done s    = Just n
                   | otherwise = go (n+1) (next s ++ todo')

-- Currently unused
linearWorkList :: forall a. Eq a =>
    IS.IntSet -> IM.IntMap a -> (Int -> IM.IntMap a -> a) -> IM.IntMap a
linearWorkList todo s0 recalc = go todo s0
  where
    go :: IS.IntSet -> IM.IntMap a -> IM.IntMap a
    go todo s | IS.null todo         = s
    go todo s | oldValue == newValue = go todo' s
              | otherwise            = go newTodo newS
      where
        (k, todo') = IS.deleteFindMin todo
        oldValue = s IM.! k
        newValue = recalc k s
        newS = IM.insert k newValue s
        newTodo = (if (k-1) `IM.member` s then IS.insert (k-1) else id) $
                  (if (k+1) `IM.member` s then IS.insert (k+1) else id) $ todo'

type WindowLengthRanges = [(Int, (Int,Int))]

possibleWindowLengths :: BitLength -> Width -> Leak -> WindowLengthRanges
possibleWindowLengths bits w leak = IM.elems result
  where
    clamp width = max 1 (min w width)

    -- positions of the window end (from the back, i.e. bits)
    windowEnds = IM.fromList $ zip [0..] $ map ((bits - 1) - ) $
                 V.toList $ V.findIndices (== M) leak

    windows = IM.keysSet windowEnds
    maxKey = IS.findMax windows

    zipIM = IM.intersectionWith (,)

    windowMax = IM.mapWithKey (\k _ -> w_max k) windowEnds
    windowMin = IM.mapWithKey (\k _ -> w_min k) windowEnds
    result = windowEnds `zipIM` (windowMin `zipIM` windowMax)

    msbIsOne = False

    -- The first window spans precisely from the MSB to the first M
    firstWinLength =  clamp (bits - pos)
      where pos = windowEnds IM.! 0

    -- minimum length. computed from right to left
    w_min k | k == 0, msbIsOne = firstWinLength
            | k == maxKey      = 1
            | otherwise        = clamp (j + w_min_j + w -i)
        where
            i       = windowEnds IM.! k
            j       = windowEnds IM.! (k+1)
            w_min_j = windowMin IM.! (k+1)

    -- maximum length. computed from left to right
    w_max k | k == 0    = if msbIsOne then firstWinLength else w
            | otherwise = clamp (i + w_max_i - w -j)
        where
            i       = windowEnds IM.! (k-1)
            j       = windowEnds IM.! k
            w_max_i = windowMax IM.! (k-1)

countPossibilities :: BitLength -> Width -> WindowLengthRanges -> Integer
countPossibilities bits w lengths = go (bits-1) 0
  where
    vec = V.fromList lengths

    pos k = fst (vec V.! k)
    windowLengthRange k = [minWin..maxWin]
      where
        (_, (minWin, maxWin)) =  vec V.! k

    go soonestOne k | k == V.length vec = 2^0
    go soonestOne k = sum
        [ countMemo k winLength
        | winLength <- windowLengthRange k
        , let firstOneOfWindow = pos k + winLength -1
        , firstOneOfWindow <= soonestOne
        ]

    -- simple memoization
    countTable = V.fromList
        [ count k winLength | k <- [0..V.length vec -1] , winLength <- [1..w] ]
    countMemo k winLength = countTable V.!  (k * w + (winLength - 1))

    count k winLength = 2^unknown * go nextPossibleOne (k+1)
      where
        firstOneOfWindow = pos k + winLength -1
        unknown = max 0 (winLength - 2)
        nextPossibleOne = firstOneOfWindow - w


testCountPossibilities :: BitLength -> Width -> Integer -> Property
testCountPossibilities bits w s = fromIntegral (length candidates) === poss
  where
    leak = leftToRight bits w s
    windowLengths = possibleWindowLengths bits w leak
    poss = countPossibilities bits w windowLengths

    mask = getHardBits bits w windowLengths
    candidates = realCandidates bits w leak mask

getWindowStarts :: WindowLengthRanges -> IS.IntSet
getWindowStarts list = IS.fromList
    [ pos + maxWin - 1
    | (pos, (minWin, maxWin)) <- list
    ]

getHardBits :: BitLength -> Width -> WindowLengthRanges -> BitMask
getHardBits bits w final_list = go 0 (nothingKnown bits)
      where
        go i !bm | i == bits = bm
                 | i `IS.member` ones    = go (i+1) (writeKnownBit i True bm)
                 | i `IS.member` zeros   = go (i+1) (writeKnownBit i False bm)
                 | i `IS.member` inRange = go (i+1) bm
                 | otherwise             = go (i+1) (writeKnownBit i False bm)

        onesOn =     IS.fromList [ pos
                                 | (pos,(minWin, maxWin)) <- final_list ]
        onesStart =  IS.fromList [ pos + minWin - 1
                                 | (pos,(minWin, maxWin)) <- final_list
                                 , minWin == maxWin ]
        zerosAfter = IS.fromList [ j
                                 | (pos,(minWin, maxWin)) <- final_list
                                 , j <- [pos + maxWin - w .. pos - 1] ]
        inRange =    IS.fromList [ j
                                 | (pos,(minWin, maxWin)) <- final_list
                                 , j <- [pos .. pos + maxWin - 1] ]

        ones  = IS.unions [ onesOn, onesStart ]
        zeros = IS.unions [ zerosAfter ]

countHardBits :: BitLength -> Width -> WindowLengthRanges -> Int
countHardBits bits w final_list = bits - sum (map uncertain final_list)
  where uncertain (_, (minWin, maxWin)) | minWin == maxWin = max 0 (maxWin - 2)
                                        | otherwise        = max 0 (maxWin - 1)

testCountHardBits bits w final_list =
    countKnownBits bits (getHardBits bits w final_list) == countHardBits bits w final_list

knownBitsFromLeak :: BitLength -> Width -> Leak -> BitMask
knownBitsFromLeak bits w leak = getHardBits bits w $ possibleWindowLengths bits w leak

testKnownBitsFromLeak :: BitLength -> Positive Integer -> Bool
testKnownBitsFromLeak bits (Positive p) = p `matches` bm
  where
    leak = leftToRight bits 4 p
    bm = knownBitsFromLeak bits 4 leak

testKnownBitsFromLeak2 :: RSAParams -> Bool
testKnownBitsFromLeak2 params
    = dp params `matches` bitmask_dp && dq params `matches` bitmask_dq
  where
    leak_dp    = leftToRight       (bits params) 4 (dp params)
    bitmask_dp = knownBitsFromLeak (bits params) 4 leak_dp
    leak_dq    = leftToRight       (bits params) 4 (dq params)
    bitmask_dq = knownBitsFromLeak (bits params) 4 leak_dq


type Candidate = (Int, Integer, Integer, Integer, Integer)

-- | An oracle is a function that takes a possible suffix (given with length
-- and value) and indicates if this suffix is possible.
type Oracle = Int -> Integer -> Bool

selectPortion :: Double -> Int -> [Int]
selectPortion h to = go 0 0
  where
    go chosen i | i > to    = []
                | f < h     = i : go (chosen + 1) (i+1)
                | otherwise =     go  chosen      (i+1)
      where f = fromIntegral chosen / fromIntegral i

selectRandomPortion :: StdGen -> Double -> Int -> [Int]
selectRandomPortion rng h to = go rng 0
  where
    go rng i | i > to    = []
             | x < h     = i : go rng' (i+1)
             | otherwise =     go rng' (i+1)
      where (x, rng') = random rng

mkHardBitOracle :: BitLength -> Double -> Integer -> Oracle
mkHardBitOracle bits h input = oracle
  where
    rng = mkStdGen (fromIntegral (input+3))
    knownBits = IS.fromList $ selectRandomPortion rng h bits
    oracle i guess
        | i `IS.member` knownBits
        = guess `testBit` i == input `testBit` i
        | otherwise
        = True

mkBlockSumOracle :: Int -> Integer -> Oracle
mkBlockSumOracle bs input = oracle
  where
    oracle i guess | j `mod` bs == 0 = guess ==? input
                   | otherwise       = True
      where
        j = i + 1
        select k = (k `div` 2^(j-bs)) `mod` 2^bs
        (==?) = ((==) `on` popCount) `on` select

testOracle :: (Integer -> Oracle) -> Positive Integer -> Positive Int ->  Bool
testOracle mkO (Positive input) (Positive i) = o i (input `mod` 2^(i+1))
  where o = mkO input

mkLeftToRightOracle bits w input = oracle
  where
   s = leftToRight bits w input

   windowLengths = possibleWindowLengths bits w s
   bitmask = getHardBits bits w windowLengths
   windowStarts = getWindowStarts windowLengths

   shouldCheck i = (i-1) `IS.member` windowStarts

   oracle i guess
        | (guess `testBit` i) `notElem` possibleBits bitmask i
        = False
        | shouldCheck i
        , let leak' = leftToRight i w guess
        , V.drop (bits - i) s /= leak'
        = False
        | otherwise
        = True

-- Recovers the bits from the leaks for p and q
lsbRecovery :: Int -> RSAParams -> (Oracle, Oracle) -> Maybe Int
lsbRecovery limit params (op, oq) = dfSearch limit s0 next done
  where
    s0 :: Candidate
    s0 = ( 0 -- last bit guessed/set; this and all later bits are known
         , 1 -- known suffix of dp
         , 1 -- known suffix of dq
         , 1 -- known suffix of p
         , 1 -- known suffix of q
         )

    next :: Candidate -> [Candidate]
    next (i, dp, dq, p, q)
        | j == (bits params) = []
        | otherwise =
            filter prune
            [ (j, dp', dq', p', q')
            | (p',dp') <- filter (pruneP j) $ (,) <$> nextP <*> nextDP
            , (q',dq') <- filter (pruneQ j) $ (,) <$> nextQ <*> nextDQ
            ]
      where
        j = i+1
        nextDP = [dp, dp `setBit` j]
        nextDQ = [dq, dq `setBit` j]
        nextP  = [p, p `setBit` j]
        nextQ  = [q, q `setBit` j]

    pruneP i (p, dp) = and
        [ (e params*dp - 1) `mod` modulus == (kp params * (p-1)) `mod` modulus
        , op i dp
        ]
      where modulus = 2^(i+1)

    pruneQ i (q, dq) = and
        [ (e params*dq - 1) `mod` modulus == (kq params * (q-1)) `mod` modulus
        , oq i dq
        ]
      where modulus = 2^(i+1)

    prune :: Candidate -> Bool
    prune (i, dp, dq, p, q)
        = and [ (p * q) `mod` modulus == n params `mod` modulus
              ]
      where modulus = 2^(i+1)

    done :: Candidate -> Bool
    done (i, dp', dq', p', q')
        = i + 1 == bits params
        && p' * q' == n params
        {-
        && Just dp' == invertMod (e params) (p'-1)
        && Just dq' == invertMod (e params) (q'-1)
        && (dp' == dp params || traceShow ('P',p',q', dp', dq', params) True)
        && (dq' == dq params || traceShow ('Q',p',q', dp', dq', params) True)
        && (dp' `matches` bitmask_dp || traceShow (bits params, dp params) True)
        && (dq' `matches` bitmask_dq || traceShow (bits params, dq params) True)
        -}

runLSBRecovery :: Int -> Width -> RSAParams -> Maybe Int
runLSBRecovery limit w params =
    let op = mkLeftToRightOracle (bits params) w (dp params)
        oq = mkLeftToRightOracle (bits params) w (dq params)
    in lsbRecovery limit params (op, oq)

main :: IO ()
main = join . customExecParser (prefs showHelpOnEmpty) $
  info (helper <*> parser)
  (  fullDesc
  <> header "Sliding right experiment"
  <> progDesc "Slides stuff around"
  <> footer "Some parameter understand range syntax in the form 1,2,3,4 or 4,8,..,2048"
  )
  where
    parser :: Parser (IO ())
    parser =
      hsubparser (mconcat
        [ command "run_recover"        recoverCommand
        , command "left_to_right"      printLTRCommand
        , command "test_hard_rules"    testHardRulesCommand
        , command "measure_leakage"    measureLeakageCommand
        , command "collision_entropy"  measureCollisionEntropyCommand
        , command "hard_soft_scatter"  hardSoftScatterCommand
        , command "leak_preinput_size" leakPreinputCommand
        , command "entropy_scatter"    entropyScatterCommand
        ])


    bitsArg = (`div` 2) <$> -- internally, we want the key length of p and q
      option auto
      (  long "bits"
         <> metavar "BITS"
         <> help "Bit length of p and q combined (usually 1024 or 2048)"
         <> value 1024
         <> showDefault
      )

    bitsRangeArg = (map (`div` 2)) <$> -- internally, we want the key length of p and q
      option (eitherReader parseRange)
      (  long "bits"
         <> metavar "BITS,.."
         <> help "Bit length of p and q combined. Range syntax allowed"
         <> value [1024]
         <> showDefaultWith showRange
      )

    knownBitsRangeArg =
      option (eitherReader parseRange)
      (  long "known-bits"
         <> metavar "PROB,.."
         <> help "Proportion of known bits in range 0...1000. Range syntax allowed"
         <> value [0,100..1000]
         <> showDefaultWith showRange
      )

    blockSumRangeArg =
      option (eitherReader parseRange)
      (  long "sum-length"
         <> metavar "INT,.."
         <> help "Lenght of blocks of which sum is known"
         <> value [1,2,3,4]
         <> showDefaultWith showRange
      )

    widthArg = option auto
         (  long "width"
         <> metavar "WIDTH"
         <> help "Width of the window (e.g. 4 or 5)"
         <> value 4
         <> showDefault
         )

    widthRangeArg = option (eitherReader parseRange)
         (  long "width"
         <> metavar "WIDTH,.."
         <> help "Width of the window (e.g. 4 or 5). Range syntax allowed."
         <> value [4]
         <> showDefaultWith showRange
         )

    iterationsArg = option auto
         (  long "iterations"
         <> metavar "N"
         <> help "Number of iterations"
         <> value 100
         <> showDefault
         )

    limitArg = option auto
         (  long "limit"
         <> metavar "N"
         <> help "Search limit"
         <> value 100000
         <> showDefault
         )

    tsvArg = switch
         (  long "tsv"
         <> help "Tab separated output (no variance)"
         )


    printLTRCommand = info
        (pure printLTR <*> bitsArg <*> widthArg<*> bitSequenceArg)
        (progDesc "Run left-to-right and print sequence")
      where bitSequenceArg = argument auto (metavar "input_sequence")

    testHardRulesCommand = info
        (pure testHardRules <*> bitsArg <*> widthArg<*> verboseArg)
        (progDesc "Verify hard bit calculation (no output = all good)")
      where verboseArg = switch (long "verbose" <> help "Show all tested data")

    recoverCommand = info
        (pure runRecover <*> bitsArg <*> widthArg<*> iterationsArg <*> limitArg )
        (progDesc "Run key recovery, and calculate search tree size")

    measureLeakageCommand = info
        (pure measureLeakage <*> bitsRangeArg <*> widthRangeArg<*> tsvArg <*> iterationsArg)
        (progDesc "Calculate the Shannon entropy rate and hard bits")

    measureCollisionEntropyCommand = info
        (pure measureCollisionEntropy <*> bitsRangeArg <*> widthRangeArg<*> tsvArg <*> iterationsArg)
        (progDesc "Calculate the collision entropy rate")

    hardSoftScatterCommand = info
        (pure hardSoftScatter <*> bitsRangeArg <*> widthRangeArg<*> iterationsArg)
        (progDesc "Draw a hard/soft bit scatter plot")

    leakPreinputCommand = info
        (pure leakPreinput <*> widthArg)
        (progDesc "Number of input sequences for given square-and-mulitply sequence")

    entropyScatterCommand = info
        (pure runScatter <*> bitsArg <*> knownBitsRangeArg <*> widthRangeArg <*> blockSumRangeArg <*>iterationsArg <*> limitArg )
        (progDesc "Simulates recovery with various oracles of given entropy, measuing tree size")

runRecover :: BitLength -> Width -> Int -> Int -> IO ()
runRecover  bits w iter limit = do
    samples <- replicateM iter $ do
       params <- generate (genRSAParams bits)
       let res = runLSBRecovery limit w params
       putStrLn $ maybe "-" show res
       return res
    let (mean, variance) = meanVariance (V.fromList (map fromIntegral (catMaybes samples)))
    putStrLn $ "-- Mean: " ++ show mean ++ " Variance: " ++ show variance

popCountCollEntropyRate :: Int -> Double
popCountCollEntropyRate w = (/fromIntegral w) $ negate $ logBase 2 $ sum [
    (fromIntegral (binom w i) / 2^w)^2
    | i <- [0..w]
    ]

binom :: Int -> Int -> Int
binom n m = fac n `div` (fac m * fac (n-m))

fac :: Int -> Int
fac n = product [1..n]

runScatter :: BitLength -> [Int] -> [Width] -> [Int] -> Int -> Int -> IO ()
runScatter  bits knownBitsRatios widths blockSums iter limit = do
    printf "leak\th\tmean\tsolved\tcalc_mean\n"
    let todo = [ (p, o, "hard_bits")
               | ratio <- sort knownBitsRatios
               , let p = fromIntegral ratio / 1000 :: Double
               , let o = mkHardBitOracle bits p
               ] ++
               [ (h, o, "ltr")
               | w <- sortBy (flip compare) widths
               , let h = [undefined, 1, 0.786, 0.652, 0.545, 0.461, 0.395, 0.345] !! w
               , let o = mkLeftToRightOracle bits w
               ] ++
               [ (h, o, "popcnt")
               | bs <- sortBy (flip compare) blockSums
               , let h = popCountCollEntropyRate bs
               , let o = mkBlockSumOracle bs
               ]
    forM_ todo $ \(h, mkO, desc) -> do
        samples <- replicateM iter $ do
           params <- generate (genRSAParams bits)
           let op = mkO (dp params)
               oq = mkO (dq params)
               res = lsbRecovery limit params (op, oq)
           -- putStrLn $ maybe "-" show res
           return res
        let (mean, variance) = meanVariance (V.fromList (map fromIntegral (catMaybes samples)))
        let solved = fromIntegral (length (filter isJust samples)) / fromIntegral iter :: Double
        printf "%s\t%.3f\t%.1f\t%.3f\t%.1g\n"
            desc h mean solved (treeSize bits h)

treeSize :: BitLength -> Double -> Double
treeSize k h = k' * (1 + (1 - 2**(k'*(1-2*h)))/(1-2**(1-2*h)))
  where k' = 2*fromIntegral k

printLargePrime :: BitLength -> Width -> IO ()
printLargePrime bits w = generate (rndPrime bits) >>= print

printRSA :: BitLength -> Width -> IO ()
printRSA bits w = generate (genRSAParams bits) >>= print

showLeak :: Leak -> String
showLeak = map go . V.toList
  where go S = '_'
        go M = 'M'

printLTR :: BitLength -> Width -> Integer -> IO ()
printLTR bits w s = putStrLn $ showLeak $ leftToRight bits w s

realCandidates :: BitLength -> Width -> Leak -> BitMask -> [Integer]
realCandidates bits w leak mask = ms'
   where ms    = allMatching mask
         ms'   = filter (\m -> leftToRight bits w m == leak) ms

reallyKnownBits :: BitLength -> Width -> Leak -> BitMask -> BitMask
reallyKnownBits bits w leak mask = mask'
   where ms'   = realCandidates bits w leak mask
         mask' = maskFromMatching ms'

testKnownBits bits w n = do
    putStrLn (showBitMask bits (fromKnownNumber n))
    let leak = leftToRight bits w n
    putStrLn (showLeak leak)
    let mask = knownBitsFromLeak bits w leak
    putStrLn (showBitMask bits mask)
    let mask' = reallyKnownBits bits w leak mask
    putStrLn (showBitMask bits mask')


testHardRules :: BitLength -> Width -> Bool -> IO ()
testHardRules bits w verbose = forM_ [2^(bits-1)..(2^bits)-1] $ \n -> do
    let leak  = leftToRight bits w n
    let mask  = knownBitsFromLeak bits w leak
    let ms    = allMatching mask
    let ms'   = filter (\m -> leftToRight bits w m == leak) ms
    let mask' = maskFromMatching ms'

    when (verbose || mask /= mask' || n `notElem` ms) $ do
        putStr $ showBitMask bits (fromKnownNumber n) ++ ": "
        putStr $ showLeak leak ++ " "
        putStr $ showBitMask bits mask ++ " "
        putStr $ showBitMask bits mask' ++ " "
        putStr $ if mask == mask' then "✓" else "☹"
        unless (n `elem` ms) $ putStr " HORROR"
        putStr "\n"

measureCollisionEntropy :: [BitLength] -> [Width] -> Bool -> Int -> IO ()
measureCollisionEntropy bitsRange wRange tsv iter= do
    when tsv $ putStrLn $ intercalate "\t" $
        words "bits width entropy"
    sequence_ [ measureCollisionEntropyOne bits w tsv iter
              | bits <- bitsRange, w <- wRange ]

measureCollisionEntropyOne :: BitLength -> Width -> Bool -> Int -> IO ()
measureCollisionEntropyOne bits w tsv iter = do
    probs <- replicateM iter doOne
    -- There are serious problems here with numerical precision
    -- and the results seem to vary a log depending on how the logarithm
    -- is calculated
    let entropy = - (logBase 2.0 (sum probs) - fromIntegral (2*bits) - logBase 2.0 (fromIntegral iter)) / fromIntegral (2*bits)
    if tsv then
        putStrLn $ intercalate "\t" $ map show [2*bits, w] ++ map show [entropy]
    else putStrLn $ "Collision entropy rate:" ++ show entropy
  where
    stats :: V.Vector Double -> [Double]
    stats samples =
        [ minimum samples ] ++
        [ weightedAvg n 4 samples | n <- [1..3]] ++
        [ maximum samples ]
    doOne = do
        dp <- fmap (.|. 1) $ randomRIO (2^(bits - 1), 2^bits - 1)
        dq <- fmap (.|. 1) $ randomRIO (2^(bits - 1), 2^bits - 1)

        let sp = leftToRight bits w dp
            wlp = possibleWindowLengths bits w sp
            hardBitsp = countHardBits bits w wlp
            possp = countPossibilities bits w wlp

            sq = leftToRight bits w dq
            wlq = possibleWindowLengths bits w sq
            hardBitsq = countHardBits bits w wlq
            possq = countPossibilities bits w wlq

            totalBits = fromIntegral (2*bits)
            prob = fromIntegral possp * fromIntegral possq
        return prob

measureLeakage :: [BitLength] -> [Width] -> Bool -> Int -> IO ()
measureLeakage bitsRange wRange tsv iter= do
    when tsv $ putStrLn $ intercalate "\t" $
        words "bits width" ++
        concatMap (\n -> [n ++ "_q" ++ show i | i <- [0..4]])
            (words "rightToLeft hardBitsLearned informationGained GMP")
    sequence_ [ measureLeakageOne bits w tsv iter
              | bits <- bitsRange, w <- wRange ]

measureLeakageOne :: BitLength -> Width -> Bool -> Int -> IO ()
measureLeakageOne bits w tsv iter= do
    (samplesRTL, samplesHard, samplesReal, samplesGMP) <- V.unzip4 . V.fromList <$> replicateM iter doOne
    if tsv then do
        putStrLn $ intercalate "\t" $
            map show [2*bits, w] ++
            map show (concatMap stats [ samplesRTL, samplesHard, samplesReal, samplesGMP])
    else do
        let (mean, variance) = meanVariance samplesHard
        let good = V.sum (V.map (\n -> if n > 0.5 then 1 else 0) samplesHard) / fromIntegral iter
        putStrLn $ "Hard bits mean:  " ++ show mean ++
                   " variance: " ++ show variance ++
                   " >50%: " ++ show good
        let (mean, variance) = meanVariance samplesReal
        let good = V.sum (V.map (\n -> if n > 0.5 then 1 else 0) samplesReal) / fromIntegral iter
        putStrLn $ "Total data mean: " ++ show mean ++
                   " variance: " ++ show variance ++
                   " >50%: " ++ show good
  where
    stats :: V.Vector Double -> [Double]
    stats samples =
        [ minimum samples ] ++
        [ weightedAvg n 4 samples | n <- [1..3]] ++
        [ maximum samples ]
    doOne = do
        dp <- fmap (.|. 1) $ randomRIO (2^(bits - 1), 2^bits - 1)
        dq <- fmap (.|. 1) $ randomRIO (2^(bits - 1), 2^bits - 1)

        let sp = leftToRight bits w dp
            wlp = possibleWindowLengths bits w sp
            hardBitsp = countHardBits bits w wlp
            possp = countPossibilities bits w wlp

            sq = leftToRight bits w dq
            wlq = possibleWindowLengths bits w sq
            hardBitsq = countHardBits bits w wlq
            possq = countPossibilities bits w wlq

            totalBits = fromIntegral (2*bits)
            hardBitsFrac = fromIntegral (hardBitsp + hardBitsq) / totalBits

            realBitsFrac = ( totalBits - logBase 2.0 (fromIntegral possp) - logBase 2.0 (fromIntegral possq) ) / totalBits

            rtlBitsFrac = ( fromIntegral $ rightToLeftBits bits w dp + rightToLeftBits bits w dq
                          ) / totalBits

            gmpBitsFrac = ( fromIntegral $ leftToRightGMPBits bits w dp + leftToRightGMPBits bits w dq
                          ) / totalBits

        return (rtlBitsFrac, hardBitsFrac, realBitsFrac, gmpBitsFrac)

hardSoftScatter :: [BitLength] -> [Width] -> Int -> IO ()
hardSoftScatter bitsRange wRange iter = do
    putStrLn $ intercalate "\t" $ words "bits width hard soft"
    forM_ bitsRange $ \bits -> forM_ wRange $ \w -> do
        pairs <- replicateM iter (doOne bits w)
        forM_ pairs $ \(h,s) ->
            putStrLn $ intercalate "\t" (map show [bits, w] ++ map show [h,s])
  where
    doOne bits w = do
        dp <- fmap (.|. 1) $ randomRIO (2^(bits - 1), 2^bits - 1)
        dq <- fmap (.|. 1) $ randomRIO (2^(bits - 1), 2^bits - 1)

        let sp = leftToRight bits w dp
            wlp = possibleWindowLengths bits w sp
            hardBitsp = countHardBits bits w wlp
            possp = countPossibilities bits w wlp

            sq = leftToRight bits w dq
            wlq = possibleWindowLengths bits w sq
            hardBitsq = countHardBits bits w wlq
            possq = countPossibilities bits w wlq

            totalBits = fromIntegral (2*bits) :: Double
            hardBitsFrac = fromIntegral (hardBitsp + hardBitsq) / totalBits

            realBitsFrac = ( totalBits - logBase 2.0 (fromIntegral possp) - logBase 2.0 (fromIntegral possq) ) / totalBits

            rtlBitsFrac = ( fromIntegral $ rightToLeftBits bits w dp + rightToLeftBits bits w dq
                          ) / totalBits

            gmpBitsFrac = ( fromIntegral $ leftToRightGMPBits bits w dp + leftToRightGMPBits bits w dq
                          ) / totalBits

        return (hardBitsFrac, realBitsFrac)

leakPreinput ::  Width -> IO ()
leakPreinput w = do
    line <- getLine
    let line' = fixFirst line
    unless (all (`elem` "SM_") line') $ do
        hPutStrLn stderr "Error: Input is not a sequence of 'S', '_' or 'M'"
        exitFailure
    let bits = length line'
        sp = V.fromList (map toStep line')
        wlp = possibleWindowLengths bits w sp
            --hardBitsp = countHardBits bits w wlp
        possp = countPossibilities bits w wlp
    print possp
  where
    toStep 'M' = M
    toStep 'S' = S
    toStep '_' = S

    -- The input may explicitly say that the first character is a 1.
    -- This code knows that, but still expects there to be a S or M.
    -- Recover whether this is a S or M from looking at the following characters.
    fixFirst ('1':xs) = if 'M' `elem` take (w - 1) xs then 'S':xs else 'M':xs
    fixFirst xs = xs


showRange :: [Int] -> String
showRange = intercalate "," . map show

parseRange :: String -> Either String [Int]
parseRange s = case splitOn "," s of
    [n1,n2,"..",n3] -> enumFromThenTo <$> readEither n1 <*> readEither n2 <*> readEither n3
    [n1,"..",n3] -> enumFromTo <$> readEither n1 <*> readEither n3
    ns -> mapM readEither ns

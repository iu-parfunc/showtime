{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -Wincomplete-uni-patterns #-}
module Showtime.Original where

import qualified Data.Foldable as Fld
import Data.List as L
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.Sequence as Seq
import Data.Sequence ((|>))
import Showtime.Lattice

#if 0
import qualified Debug.Trace
#endif

--------------------------------------------------------------------------------

-- Optional debugging messages:
trace :: String -> a -> a
#if 0
trace = Debug.Trace.trace
#else
trace _ x = x
#endif

traceM :: Applicative f => String -> f ()
traceM s = seq (trace s) (pure ())

--------------------------------------------------------------------------------

-- | Time should be a non-negative rational.  Here we use 'Double's
-- only because they print more concisely.
type Time = Double -- LH refinement: non-negative

-- | The vector of per-thread times.
--
-- NOTE: There are two competing notions of what it means for thread @i@
-- to have time @T@.
--
-- 1. Thread @i@ is on "round" @T@, and will produce event(s) tagged @T@
--    until it updates it clock to @T+1@. No future events @<T@.
--
-- 2. Thread @i@ will never send any event tagged @<=T@. Any event will
--    have to bump the clock by some amount first.
--
-- IMHO the first is more natural with a discrete formulation, and the
-- second with a continuous one.  Here we use the continuous
-- formulation and the second option.
type TimeVec = [Time]

epsilon :: Time
epsilon = 0.1

-- | Distinct time offset for a particular thread.
myEpsilon :: TID -> Time
myEpsilon (TID n) = fromIntegral (n+1) * epsilon

-- | \"The end of time\" - need to modify 'Time' to include a max bound.
inf :: Time
inf = 100000

-- | 'Time' consumed by the open operation itself.
openTimeDelta :: Time
openTimeDelta = 1

-- | How long do we reserve for, once we access the resource?  (Aka
-- epoch or quanta.)
showLen :: Time
showLen = 10

-- | For simplicity, assume a fixed number of processors/threads:
numProcs :: Int
numProcs = 3

newtype TID = TID Int deriving (Eq, Show, Ord, Read, Enum)

fromTID :: TID -> Int
fromTID (TID i) = i

type Log = Set (Time, TID)

-- | A partial function that maps the current (local) time onto the
-- next when the resource is free.
-- type NextExpiry = (Time -> Maybe Time)

-- | The state of the lvar is a pair.
data State = State TimeVec Log
  deriving (Show, Ord, Eq)

bound :: Int -> State -> State
bound n (State tv lg) = State (L.take n tv) lg

instance JoinSemiLattice State where
  -- Note, could make this partial to encode the constraint that we
  -- should never learn about new join events that are *in the past*
  -- based on our current clock. This constraint needs to live
  -- somewhere.
  State t1 l1 \/ State t2 l2 =
    State (zipWith max t1 t2) (S.union l1 l2)

instance BoundedJoinSemiLattice State where
  -- FIXME: adding "implicit zeros" for a sparse representation would
  -- fix the need for an infinite data structure here.
  bottom = State [ myEpsilon i | i <- [TID 0..]] S.empty

-- Proofs should be easy:
--   associative:
--   commututative:
--   idempotent:
--   bottom identity

-- Public Interface ------------------------------------------------------------

tick :: TID -> State -> State
tick = tickN 1

myTime :: TID -> State -> Time
myTime (TID i) (State tv _) = tv !! i

-- | Gain access to the resource. May advance our clocks to represent
-- logical waiting, and may "block" for more information by returning Nothing.
--
-- POLICY: may return a 'State' in which our thread is advanced into the
-- next show, time-wise, but it is STILL waiting on other threads to
-- reach the showtime to stabilize participants and establish that it is LMIC.
-- (That is, the 'Open' 'Op' cannot yet reduce.)
--
-- RETURNS: the new 'State', and the start 'Time' of the show we are joining.
openResource :: TID -> State -> Maybe (State, Time)
openResource me s0@(State tv lg) =
    let myt0  = myTime me s0
        _myt1 = myt0 + openTimeDelta
        -- Register our join attempt in the log:
        lg2 = S.insert (myt0, me) lg
        s1  = tickN openTimeDelta me (State tv lg2) in
    trace (show me ++ ": openResource: new log, new state: " ++ show (lg2, s1)) $ do
      t1 <- getNextShow me s1
      -- case readParticipants t1 s1 of
      --   Nothing -> trace (show me ++ ": openResource: other clocks not up to showtime "
      --                      ++ show t1 ++ " in state:\n  " ++ show s1)
      --              Nothing
      --   Just _ ->
      let myJoinTime = t1 + myEpsilon me
      trace (show me ++ ": openResource: Computed next show " ++ show t1
             ++ " with my offset: " ++ show myJoinTime) $
            if t1 > myt0
            then return (tickN (myJoinTime - myt0) me s1, t1)
            else return (s1, t1)


-- Implementation --------------------------------------------------------------

-- | MONOTONIC (in 'State' argument): What is the set of participants
-- tha need to be synced/ordered when accessing the resource at the
-- specified logical time.
readParticipants :: Time -> State -> Maybe (Set TID)
readParticipants t (State tv lg)
 | any (< t) tv = Nothing
 | otherwise = Just $
     -- No LEAVE events yet, only join, so this is simple:
     S.fromList (L.map snd (unstableLogPrefix t lg))

-- | MONOTONIC (in 'State' argument): From the perspective of our
-- current time, what is the next time that we can gain access to the
-- resource. Note that this time may be in the past if we CURRENTLY
-- have access to the resource.
getNextShow :: TID -> State -> Maybe Time
getNextShow myi s0@(State tv lg) =
  trace (show myi ++ ": getting next show at time " ++ show myt
         ++ " from times " ++ show times ++ " in state " ++ show s0
         ++ " result = " ++ show result)
        result
  where
    -- If the show we WOULD seem to be part of is based on incomplete
    -- information, then we must block until more information is available:
    -- result, tentative :: Maybe Time
    -- result = case tentative of
    --            Nothing -> Nothing
    --            Just tm -> if L.any (< tm) tv
    --                       then Nothing
    --                       else tentative

    -- Grab the first time that we can make it to:
    result :: Maybe Time
    result = ourShow (dropWhile (< (myt-showLen)) times)

    ourShow :: [Time] -> Maybe Time
    ourShow [] = Nothing
    ourShow (t:rst)
     | t < myt
     = do set <- readParticipants t s0 -- Who was in at the START of the show.
          trace (" <getNext> " ++ show myi ++ " is checking for membership in "
                 ++ show set ++ " i.e. participants in show starting at " ++show t) $
                if S.member myi set
                then return t
                else ourShow rst
     | otherwise
     = trace (" <getNext> got winner " ++ show t) $
             Just t

    myt :: Time
    myt = myTime myi s0

    times :: [Time]
    times = showtimes (L.map fst pref)

    -- The STABLE prefix is the one that is pruned to the GMIC:
    pref :: [(Time, TID)]
    pref = unstableLogPrefix (minimum tv) lg

-- | Simple SEQUENTIAL process that describes the show start times as a
-- function of join request times.
showtimes :: [Time] -> [Time]
showtimes ls = open ls
  where
    open :: [Time] -> [Time]
    open []       = []
    open (t0:rst) = t0 : closed (t0 + showLen) rst

    closed :: Time -> [Time] -> [Time]
    closed _expiry [] = []
    closed expiry (t1:rst)
      | t1 < expiry = expiry : closed (expiry + showLen) (dropWhile (< expiry) rst)
      | otherwise   = open (t1:rst)


-- | Take events up to AND INCLUDING the current moment in time.
-- The answer is only FINAL iff all local clocks have reached this time.
unstableLogPrefix :: Time -> Log -> [(Time, TID)]
unstableLogPrefix t lg =
  trace ("  log prefix of " ++ show lg ++ ", time " ++ show t ++ " yields " ++ show set) $
        S.toList set
  where
    set :: Log
    set = S.takeWhileAntitone (\(ti,_) -> ti <= t) lg


tickN :: Time -> TID -> State -> State
tickN delta (TID i) (State tl l1)
  | delta >= 0 = State (fr ++ (old + delta) : back) l1
  | otherwise  = error ("impossible, cannot tick a negative amount: " ++ show delta)
  where
    fr, back :: [Time]
    old :: Time
    (fr, old : back) = L.splitAt i tl

ex1 :: Maybe State
ex1 = do
   let s1 = tickN 5 (TID 0) $
            tickN 3 (TID 1) $
            tickN 4 (TID 2) $ bound numProcs bottom
   (s2,_) <- openResource (TID 1) s1  -- access at time 3
   -- In this excessively conservative prototype, we must tick (TID 2) forward as well:
   s3 <- pure $ tick (TID 2) s2
   (s4,_) <- openResource (TID 1) s3  -- access at time 4

   -- s5 <- pure $ tickN 3 (TID 0) -- tick forward into the show

   s5 <- pure $ tick (TID 1) s4
   s6 <- pure $ tick (TID 2) s5
   (s7,_) <- openResource (TID 0) s6  -- access at time 5

   return s7

-- Monadic formulation
--------------------------------------------------------------------------------

-- It would be easy to put a monadic interface on top of the above, to
-- write more natural programs...


-- Simple programs to feed interpreter/model checker
--------------------------------------------------------------------------------

-- | A very simple representation of programs. Each thread performs a
-- finite series of 'Op's.
type Prog = [[Op]]
data Op = Compute Time
        | Open
        ----------------------------------------
        -- Internal states:
        | BlockedOpen { whichShow :: Time }
          -- ^ Annotated with the START time of the show the op is waiting for.
  deriving (Show, Ord, Eq, Read)

-- | A run's result is defined as the linear sequence of operations
-- applied to the resource.
type Oplog = Seq.Seq OpInst
data OpInst = OpInst TID Time Op deriving (Show, Ord, Eq, Read)

-- Try1:
{-
-- | A non-deterministic interpreter that returns a stream of possible
-- outcomes.
interp :: Prog -> [Oplog]
interp prgs = go bottom (zip [TID 0..] prgs)
  where
  -- Inefficient: better to do BFS and track the set of explored states:
  go s0@(State tv lg) ls =
   do let live = L.filter (not . L.null . snd) ls
          len  = L.length live
      if L.null live then return Seq.empty else do
        thrd <- [0..len-1]
        trace ("Executing thread " ++ show thrd ++ " of " ++ show live) $
          case L.splitAt thrd live of
            (frnt, (myid, op:rst) : bk)     ->
              let myt       = myTime myid s0
                  remaining = (frnt ++ (myid, rst) : bk) in
              case op of
                Open ->
                  case readParticipants myt s0 of
                   Nothing -> trace ("Can't resolve participants " ++ show (thrd, s0)) []
                              -- go s0 live -- fizzle and keep going.
                   Just s -> if amLMIC myid s s0
                             -- This models actually committing the operation:
                             then (|> (myid,Open)) <$> go s0 remaining
                             else go s0 live
                Compute dt ->
                  go (tickN dt myid s0) remaining

-- t0 = interp [[Open]]
-- t1 = interp [[Open],[Open]]
-- t2 = interp [[Compute 10,Open],[Open]]
-}

-- | Do I have the local minumim instruction count of the given set of threads?
amLMIC :: TID -> Set TID -> State -> Bool
amLMIC myi set st = all (>= myt) oths
  where
    myt :: Time
    myt = myTime myi st

    oths :: [Time]
    oths = [ myTime i st | i <- S.toList set]

-- Try2: a simple model-checker that explores all states.
------------------------------------------------------------


-- | Returns two sets: *complete* states, and *timed-out* states that
-- did not evaluate all threads' operations before running out of fuel.
interp2 :: Prog -> ( Set (State, Oplog)
                   , Set (State, Prog, Oplog) )
interp2 ops =
    ( S.map (\(a, _, b)  -> (a, b)) done
    , S.map (\(s, p, ol) -> (s, dense numThreads p, ol)) unreached )
  where
    numThreads :: Int
    numThreads = length ops

    done :: Set Conf
    done = S.filter (\(s, p, _) -> isProgDone s p) final

    -- HACK: need a better solution for bottom that doesn't fix the number of threads:
    bot' :: State
    bot' = case bottom of
             State tv lg -> State (L.take numThreads tv) lg

    final, unreached :: Set Conf
    (final, unreached) = explore defaultFuel S.empty
                           (S.singleton (bot',zip [TID 0..] ops, Seq.empty))

    -- Search K levels out in the graph:
    explore :: Int -> Set Conf -> Set Conf -> (Set Conf, Set Conf)
    explore fuel visited next
        | fuel == 0 || S.null next = (visited, next)
        | otherwise =
          trace ("\n     **** EXPLORE ****   visited "
                 ++ show (S.size visited) ++ " next up: " ++ show (S.size next)) $
                let next'    = S.unions $ L.map expand (S.toList next)
                    visited' = S.union visited next
                    whatsnew = S.difference next' visited'
                in explore (fuel - 1) visited' whatsnew

    -- | Enumerate reachable states by one reduction.
    expand :: Conf -> Set Conf
    expand (s0, ps0, ol) =
      trace ("\n EXPAND STATE! Live threads " ++ show ps0 ++ " state " ++ show s0) $
      S.fromList $ catMaybes $
      [ -- TODO: This case is partial!
        case L.splitAt thrd ps0 of
         -- The thread is tapped out of ops. Bump its clock to show it won't be
         -- doing anything else:
         (frnt, (myid, []) : bk) ->
           Just (tickN inf myid s0, frnt ++ bk, ol)
         (frnt, (myid, op:rst) : bk) ->
           let _myt      = myTime myid s0
               remaining = (frnt ++ (myid, rst) : bk) -- Ops left IF we reduce.
           in case op of
              Open -> -- May not reduce yet; must be able to ascertain next showtime.
                case openResource myid s0 of
                  Nothing -> trace (" X Can't openResource now " ++ show (myid, s0))
                             Nothing
                  Just (s1, showStrt) ->
                    -- We go to the BlockedOpen state even IF it could reduce immediately:
                    Just (s1, frnt ++ (myid, BlockedOpen showStrt : rst) : bk, ol)

              BlockedOpen showStrt ->
                -- We must make sure that all threads have reached the start of the show
                -- to ensure there will be no more joiners.
                case readParticipants showStrt s0 of
                  Nothing -> trace (show myid ++ ": expand: other clocks not up to showtime "
                                              ++ show showStrt ++ " in state:\n  " ++ show s0
                                              ++ " oplog " ++ show ol)
                                   Nothing
                  Just locals ->
                    -- Here's the MAGIC, we don't need to wait for
                    -- GMIC in order to reduce this operation, LMIC suffices:
                    if amLMIC myid locals s0
                    then -- REDUCE!
                         Just (s0, remaining, ol |> (OpInst myid (myTime myid s0) Open))
                    else Nothing

              -- Compute ops are non-blocking, they can always step:
              Compute dt -> Just (tickN dt myid s0, remaining, ol)
      | thrd <- [0..L.length ps0 - 1] -- Try to take a step on each thread.
      ]

-- | TODO: switch to counting individual expand calls, not levels in BFS
defaultFuel :: Int
defaultFuel = 15

-- | Is a program terminated, or still running?
-- Definition 1: all operations have completed.
-- Definition 2: all threads have explicitly terminated.
isProgDone :: State -> LabeledProg -> Bool
isProgDone _s p = all (L.null . snd) p
-- isProgDone (State tv _) _ = all (>= inf) tv  -- Doesn't work with infinite TimeVec.
-- isProgDone (State tv _) p = L.null p ||
--                             (all (L.null . snd) p &&
--                              all (>= inf) (L.take (maximum (L.map (fromTID . fst) p)) tv))

-- | Book-keeping, keeping track of a sparse version of 'Prog'.
type LabeledProg = [(TID, [Op])]

-- | Convert from sparse to dense representation.
dense :: Int -> LabeledProg -> Prog
dense n prs = [ maybe [] id (M.lookup (TID i) mp) | i <- [0..n-1] ]
  where
    mp :: Map TID [Op]
    mp = M.fromList prs

-- | A configuration while we are evaluating.
type Conf = (State, LabeledProg, Oplog)

summarize :: ( Set (State, Oplog)
             , Set (State, Prog, Oplog) )
          -> (Maybe Oplog, Int)
summarize (s1,s2) =
  case S.toList logs of
    [ans] -> (Just ans, S.size s2)
    []    -> (Nothing, S.size s2)
    ls    -> error $ "Impossible! Nondeterministic outcome!:\n" ++ unlines (L.map show ls)
  where
    logs :: Set Oplog
    logs = S.map snd s1

-- | A simple summary of a run, what order did threads issue operations.
threadOrder :: Prog -> [Int]
threadOrder p =
  case summarize (interp2 p) of
    (Nothing,n) -> error $ "Not enough fuel to reduce, leftover states: " ++ show n
    (Just ol,_) -> L.map (\(OpInst (TID i) _ _) -> i) (Fld.toList ol)

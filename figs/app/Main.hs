{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}

module Main where

import           Control.Monad (zipWithM, when, forM_, foldM_)
import           Control.Monad.IO.Class (liftIO)
import           Control.Monad.Trans.RWS.Lazy hiding (local)
import           Data.List (maximumBy, intercalate)
import           Data.Maybe (fromJust)
import           Data.Ord (comparing)
import           Data.Tree
import qualified Data.Tree.Zipper as Z
import qualified Data.Vector as V
import           Debug.Trace
import           Diagrams.Backend.Rasterific
import           Diagrams.Prelude
import           Diagrams.TwoD.Layout.Tree
import           System.Directory (getCurrentDirectory)
import           System.Random.MWC
import           System.Random.MWC.Distributions (uniformShuffle, categorical)
import           Text.Printf (printf)

----------------------------------------------------------------------
-- Abstraction for a two-player game
--
----------------------------------------------------------------------

class Game a where
  draw :: a -> Diagram B
  next :: a -> Bool -> [a]
  scores :: a -> (Int, Int)

----------------------------------------------------------------------
-- Generating a Full or Random game tree
--
----------------------------------------------------------------------

fullGameTree :: Game g => g -> Tree g
fullGameTree g = unfoldTree (
  \(g, player1) -> (g, map (, not player1) $ next g player1)) (g, True)

-- Generate full game tree and randomly select some leaves
-- prune the rest
randomGameTree :: Game g => g -> IO (Tree g)
randomGameTree g = withSystemRandom $ \gen -> unfoldTreeM (f gen) (g, True)
  where f gen (g, player1) = do
          let children = next g player1
          if null children
            then return (g, [])
            else do
              let childv = V.fromList children
              i <- asGenIO (uniformR (1, V.length childv)) gen
              cs <- uniformShuffle childv gen
              return (g, map (, not player1) $ take i (V.toList cs))

----------------------------------------------------------------------
-- Abstracted Minimax
--
----------------------------------------------------------------------

data MM g = MM
  {
    game :: g
  , best :: Int
  }

drawMMTree :: Game g => Tree (MM g) -> Diagram B
drawMMTree = renderTree f (~~) . symmLayout' (with & slHSep .~ 6 & slVSep .~ 5)
  where f x = (text (show (best x)) # fontSize (local 0.5)
           <> square 1 # fc cyan) === strutY 0.1 === draw (game x)

minimax :: Game g => Tree g -> [Tree (MM g)]
minimax root = snd $ evalRWS (go root True) () (Z.fromTree $ fmap (\t -> MM t 0) root)
  where go t player1
          | null (subForest t) = do
              -- set the best score
              let (p1,p2) = scores . rootLabel $ t
              setScoreAndReport $ if not player1 then p1 else p2
          | otherwise = do
              ss <- zipWithM (\i t -> do
                                 modify (fromJust . Z.childAt i)
                                 res <- go t (not player1)
                                 modify (fromJust . Z.parent)
                                 return res
                             ) [0..] (subForest t)
              setScoreAndReport $ if player1 then maximum ss else minimum ss
        setScoreAndReport :: Int -> RWS () [Tree (MM g)] (Z.TreePos Z.Full (MM g)) Int
        setScoreAndReport s = do
          modify (Z.modifyTree (\x@Node{rootLabel=r} -> x{rootLabel = r{best=s}}))
          get >>= tell . (:[]) . Z.toTree
          return s

----------------------------------------------------------------------
-- Abstracted Monte Carlo Tree Search
--
----------------------------------------------------------------------

class MCTS a where
    select :: [a] -> (Int, a, Diagram B)
    -- | second pos of tuple is a function that will be applied to selected node
    rollout :: a -> Bool -> ([(a, Double)], a -> a, Diagram B)
    backup :: Maybe a -> a -> (a, Diagram B)
    drawNode :: a -> Diagram B

drawMCTS :: (Show a, Eq a, MCTS a)
         => a -> Double -> Double -> FilePath -> Int -> IO ()
drawMCTS m sx sy dir niter = withSystemRandom $ \gen -> do
  (\f -> foldM_ f (Z.fromTree $ Node m []) [1..niter]) $ \z i -> do
    (z, ds) <- execRWST mcts gen z
    forM_ ds $ \(suffix, d) -> do
      traceShowM("                   " ++ show (dir, i, suffix))
      let fp = printf "%s/%03d%s.pdf" dir i suffix
      renderRasterific fp (dims2D sx sy) $
        strutY 1 ===
        strutX 1 ||| text ("Iteration " ++ show i) # bold === strutY 2 === d ||| strutX 1 ===
        strutY 1
    return z

mcts :: (Show a, Eq a, MCTS a)
     => RWST GenIO [(String, Diagram B)] (Z.TreePos Z.Full a) IO ()
mcts = do
  d <- selection (0 :: Int)
  expansion d
  backpropogate (0 :: Int) Nothing
  where selection depth = do
          traceShowM ("<<<<<< SELECTION", depth)
          hasChildren <- gets Z.hasChildren
          if hasChildren
            then do
              t <- gets Z.tree
              let (i, node, d) = select (map rootLabel (subForest t))
              traceShowM ("selection", hasChildren, i, rootLabel t, node)
              -- print diagram
              dt <- gets (drawMCTSTree node . Z.toTree)
              tell [(printf "A%03d" depth, vsep 0.5 [d, dt])]
              modify (Z.setLabel node . fromJust . Z.childAt i)
              selection (depth+1)
            else return depth

        expansion depth = do
          t <- gets Z.tree
          let (xs, func, d) = rollout (rootLabel t) (even depth)
              (nodes, weights) = unzip xs
          when (not (null xs)) $ do
            modify (Z.modifyTree (\x -> x{subForest = map (\n -> Node n []) nodes}))
            traceShowM ("weights", weights)
            i <- ask >>= liftIO . categorical (V.fromList weights)
            -- print diagram
            let chosen = func (nodes !! i)
            traceShowM ("chosen", chosen)
            modify (Z.setLabel chosen . fromJust . Z.childAt i)
            dt <- gets (drawMCTSTree chosen . Z.toTree)
            tell [(printf "A%03d" depth, vsep 1 [d, dt])]
            expansion (depth+1)

        backpropogate depth prev = do
          cur <- gets (rootLabel . Z.tree)
          let (node, d) = backup prev cur
          modify (Z.setLabel node)
          -- print diagram
          dt <- gets (drawMCTSTree node . Z.toTree)
          tell [(printf "B%03d" depth, vsep 1 [d, dt])]
          isroot <- gets Z.isRoot
          when (isroot) $ do
            gets (rootLabel . Z.tree) >>= \x -> traceShowM (">>>>>>>> END", x)
          when (not isroot) $ do
            modify (fromJust . Z.parent)
            backpropogate (depth+1) (Just node)

        drawMCTSTree sel =
          renderTree (\t -> if sel == t
                            then circle 0.5 # fc red === drawNode t
                            else drawNode t) (~~) .
          symmLayout' (with & slHSep .~ 10 & slVSep .~ 5)

----------------------------------------------------------------------
-- Greedy-coins game
--
----------------------------------------------------------------------

data GreedyCoins = GreedyCoins
  {
    board :: [Int]
  , total :: (Int, Int)
  } deriving (Eq, Show)

instance Game GreedyCoins where
  draw g =
    let coin n = text (show n) <> circle 1 # fc yellow
    in vsep 0.1 $ map centerX [
      ((text $ (show . fst $ total g) ++ " : " ++ (show . snd $ total g)) # fontSize (local 0.5) `atop` rect 3 0.8 # fc grey),
      hcat (map coin (board g))]
  next g player1
    | null (board g) = []
    | null (tail (board g)) = [g{board = tail (board g), total = playerScore (head (board g))}]
    | otherwise = [g{board = tail (board g), total = playerScore (head (board g))},
                   g{board = init (board g), total = playerScore (last (board g))}]
    where playerScore x = if player1 then (a + x, b) else (a, b + x)
          (a, b) = total g
  scores = total

----------------------------------------------------------------------
-- MCTS: Vanilla
--
-- Note: select should be a draw from distribution but using max here
-- since select is pure.
----------------------------------------------------------------------

data Vanilla g = Vanilla
  {
    vPayout :: Double
  , vCurPayout :: Double
  , vVisits :: Double
  , vState :: g
  } deriving (Eq, Show)

instance Game g => MCTS (Vanilla g) where
  select xs = if all_visited then (i, node, d) else (rand, rand_node, rand_d)
    where all_visited = all ((> 0) . vVisits) xs
          rand = fst . head . filter ((==0) . vVisits . snd) $ zip [0..] xs
          rand_node = xs !! rand
          i = fst . maximumBy (comparing snd)
            . zipWith (\i x -> (i, vPayout x / vVisits x)) [0..] $ xs
          node = xs !! i
          d = text ("Selection: arg max {" ++ intercalate ", " (map f xs) ++ "}") # fontSizeL 0.5
          f x = printf "%f" (vPayout x / vVisits x)
          rand_d = text "Selection: picking unvisited"

  rollout x player1 =
    let xs = [(Vanilla 0 0 0 g, 1) | g <- next (vState x) player1]
        d = text ("Expansion: draw ~ " ++ intercalate ", " (replicate (length xs) "1")) # fontSizeL 0.5
    in (xs, id, d)

  backup Nothing x = (x', d)
    where d = text ("Evaluation: Payout = " ++ show (vCurPayout x')) # fontSizeL 0.5
          s = fromIntegral $ fst (scores (vState x))
          x' = x{vCurPayout = s,
                 vPayout = s,
                 vVisits = vVisits x + 1}
  backup (Just y) x = (x', d)
    where d = text ("Backup: Accumulated Payout = " ++ show (vPayout x) ++ " + " ++ show (vCurPayout y)) # fontSizeL 0.5
          x' = x{vPayout = vPayout x + vCurPayout y,
                 vCurPayout = vCurPayout y,
                 vVisits = vVisits x + 1}

  drawNode x = vsep 0.3 [
    text (printf "N=%0.0f; P=%0.2f" (vVisits x) (vPayout x / vVisits x)) # fontSizeL 0.3 <>
    rect 4 0.5 # fc lightgray # lwL 0.01,
    draw (vState x)]

----------------------------------------------------------------------
-- MCTS: Upper Confidence Trees
--
----------------------------------------------------------------------

data UCT g = UCT
  {
    uctPayout :: Double
  , curPayout :: Double
  , uctVisits :: Double
  , uctState :: g
  } deriving (Eq, Show)

instance Game g => MCTS (UCT g) where
  -- mean payout + upperbound
  select xs = if all_visited then (i, node, d) else (rand, rand_node, rand_d)
    where all_visited = all ((> 0) . uctVisits) xs
          rand = fst . head . filter ((==0) . uctVisits . snd) $ zip [0..] xs
          rand_node = xs !! rand
          i = fst . maximumBy (comparing snd)
            . zipWith (\i x -> (i, ub x)) [0..] $ xs
          node = xs !! i
          total = sum (map uctVisits xs)
          z = 2 * log total
          ub x = uctPayout x / uctVisits x + sqrt (z/uctVisits x)
          d = text ("Selection: arg max {" ++ intercalate ", " (map f xs) ++ "}") # fontSizeL 0.5
          f x = printf "%f/%f + sqrt((2ln %f)/%f)" (uctPayout x) (uctVisits x) total (uctVisits x)
          rand_d = text "Selection: picking unvisited"

  rollout x player1 =
    let xs = [(UCT 0 0 0 g, 1) | g <- next (uctState x) player1]
        d = text ("Expansion: draw ~ " ++ intercalate ", " (replicate (length xs) "1")) # fontSizeL 0.5
    in (xs, id, d)

  backup Nothing x = (x', d)
    where d = text ("Evaluation: Payout = " ++ show (curPayout x')) # fontSizeL 0.5
          s = fromIntegral $ fst (scores (uctState x))
          x' = x{curPayout = s,
                 uctPayout = s,
                 uctVisits = uctVisits x + 1}
  backup (Just y) x = (x', d)
    where d = text ("Backup: Accumulated Payout = " ++ show (uctPayout x) ++ " + " ++ show (curPayout y)) # fontSizeL 0.5
          x' = x{uctPayout = uctPayout x + curPayout y,
                 curPayout = curPayout y,
                 uctVisits = uctVisits x + 1}

  drawNode x = vsep 0.3 [
    text (printf "N=%0.0f; P=%0.2f" (uctVisits x) (uctPayout x / uctVisits x)) # fontSizeL 0.3 <>
    rect 4 0.5 # fc lightgray # lwL 0.01,
    draw (uctState x)]

----------------------------------------------------------------------
-- MCTS: Alpha Go Style
--
-- Allows selection priors
-- Can use a heavy rollout
-- Uses value prediction to combine with actual value
----------------------------------------------------------------------

data AlphaGoStyle g = AlphaGoStyle
  {
    goPrior :: Double
  , goCurPayout :: Double
  , goPayout :: Double
  , goVisits :: Double
  , goPred :: Double
  , goState :: g
  } deriving (Eq, Show)

----------------------------------------------------------------------
-- MCTS: Alpho Go Style applied to GreedyCoints
--
-- heuristic used for fast-rollout, value pred and policy network is
-- prortional to cur_score + total of remaining board (-one coin)
----------------------------------------------------------------------

greedycoins_action_prob gs player1 = map (/sum totals) totals
  where totals = map (\g -> fromIntegral $
                       (if player1 then fst (scores g) else snd (scores g)) + remaining_board g
                     ) gs

remaining_board g | null (board g) = sum (board g)
                  | otherwise = sum (board g) - max (head (board g)) (last (board g))

value_prob g player1 = fromIntegral numer / fromIntegral (p1 + p2 + sum (board g))
  where numer = (if player1 then p1 else p2) + remaining_board g
        (p1, p2) = scores g

instance MCTS (AlphaGoStyle GreedyCoins) where
  select xs = if all_visited then (i, node, d) else (rand, rand_node, rand_d)
    where all_visited = all ((>0) . goVisits) xs
          rand = fst . head . filter ((==0) . goVisits . snd) $ zip [0..] xs
          rand_node = xs !! rand
          discountedPriors = map (\x -> goPrior x / (1 + goVisits x)) xs
          probPriors = map (/sum discountedPriors) discountedPriors
          meanPayouts = map (\x -> goPayout x / goVisits x) xs
          i = fst . maximumBy (comparing snd) $ zip [0..] $ zipWith (+) probPriors meanPayouts
          node = xs !! i
          d = text ("Selection: arg max {" ++
                    intercalate ", " (zipWith (\a b -> show a ++ "+" ++ show b) meanPayouts probPriors)
                   ) # fontSizeL 0.5
          rand_d = text "Selection: picking unvisited"

  rollout x player1 =
    let gs = next (goState x) player1
        action_probs = greedycoins_action_prob gs player1
        d = text ("Expansion: draw ~ " ++ intercalate ", " (map (printf "%.2f") action_probs)) # fontSizeL 0.5
        set_pred_value y = y{goPred = if goPred x == 0
                                      then value_prob (goState x) player1
                                      else goPred x}
    in (zipWith (\g p -> (AlphaGoStyle{goPred=0,
                                       goPrior=p,
                                       goState=g,
                                       goVisits=0,
                                       goCurPayout=0,
                                       goPayout=0}, p)) gs action_probs, set_pred_value, d)

  backup Nothing x = (x', d)
    where d = text (printf "Evaluation: L=0.3; Payout=%.3f*L * (1-L)*%0.3f"
                    (goPred x) s) # fontSizeL 0.5
          p1 = fromIntegral (fst (scores (goState x)))
          p2 = fromIntegral (snd (scores (goState x)))
          s | p1 > p2 = 1
            | otherwise = 0
          val = goPred x * 0.3 + s * 0.7
          x' = x{goCurPayout = val,
                 goPred = 0,
                 goPayout = val,
                 goVisits = goVisits x + 1}
  backup (Just y) x = (x', d)
    where d = text ("Backup: Accumulated Payout = " ++
                    show (goPayout x) ++ " + " ++
                    show (goCurPayout y)) # fontSizeL 0.5
          x' = x{goPayout = goPayout x + goCurPayout y,
                 goCurPayout = goCurPayout y,
                 goPred = 0,
                 goVisits = goVisits x + 1}

  drawNode x = vsep 0.3 [
    text (printf "N=%0.0f; P=%0.2f; Prior=%0.2f; v(sL)=%0.2f"
          (goVisits x) (goPayout x / goVisits x) (goPrior x) (goPred x)
         ) # fontSizeL 0.3 <>
    rect 7 0.5 # fc lightgray # lwL 0.01,
    draw (goState x)]

----------------------------------------------------------------------
-- Misc
--
----------------------------------------------------------------------

drawGameTree :: Game g => Tree g -> Diagram B
drawGameTree = renderTree draw (~~) . symmLayout' (with & slHSep .~ 6 & slVSep .~ 3)

main :: IO ()
main = do
  let g = GreedyCoins [10,3,1,2,7] (0, 0)
  dir <- getCurrentDirectory

  -- One game
  let play g (player1, i) = [Node (next g player1 !! i) []]
      z = foldl (\z i ->
                   fromJust $
                   Z.childAt 0 (Z.modifyTree (\n -> n{subForest = play (rootLabel n) i}) z)
                ) (Z.fromTree $ Node g []) (zip (cycle [True,False]) [0,1,0,1,0])
  renderRasterific (printf "%s/examples/one.pdf" dir) (dims2D 100 200) $
    drawGameTree (Z.toTree z)

  -- Full Game Tree
  renderRasterific (printf "%s/examples/full.pdf" dir) (dims2D 1500 500) $
    drawGameTree (fullGameTree g)

  -- Minimax
  forM_ (zip [(0::Int)..] $ minimax (fullGameTree g)) $ \(i,t) ->
    renderRasterific (printf "%s/examples/minimax/%d.pdf" dir i) (dims2D 1500 1500) (drawMMTree t)

  -- Vanilla
  drawMCTS (Vanilla{vPayout=0,
                    vCurPayout=0,
                    vVisits=0,
                    vState=g}) 1000 1500 (dir ++ "/examples/vanilla") 3

  -- UCT
  drawMCTS (UCT{uctPayout=0,
                curPayout=0,
                uctVisits=0,
                uctState=g}) 1000 1500 (dir ++ "/examples/uct") 3

  -- AlphaGo
  drawMCTS (AlphaGoStyle{goPrior=0,
                         goCurPayout=0,
                         goPayout=0,
                         goVisits=0,
                         goPred=0,
                         goState=g}) 1000 1500 (dir ++ "/examples/alphago") 3

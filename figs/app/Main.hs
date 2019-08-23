{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Debug.Trace
import Data.Tree
import Diagrams.Prelude
import Diagrams.Backend.Rasterific
import Diagrams.TwoD.Layout.Tree
import qualified Data.Tree.Zipper as Z
import Control.Monad (zipWithM, when, forM_, foldM_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.RWS.Lazy hiding (local)
import Data.Maybe (fromJust)
import System.Random.MWC
import System.Random.MWC.Distributions (uniformShuffle, categorical)
import qualified Data.Vector as V
import Data.Ord (comparing)
import Data.List (maximumBy, intercalate)
import Text.Printf (printf)

data GreedyCoins = GreedyCoins
  {
    board :: [Int]
  , total :: (Int, Int)
  } deriving (Eq, Show)

class Game a where
  draw :: a -> Diagram B
  next :: a -> Bool -> [a]
  scores :: a -> (Int, Int)

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

class MCTS a where
    select :: [a] -> (Int, a, Diagram B)
    rollout :: a -> Bool -> ([(a, Double)], Diagram B)
    backup :: Maybe a -> a -> (a, Diagram B)
    drawNode :: a -> Diagram B

drawMCTS :: (Show a, Eq a, MCTS a) => a -> Double -> Double -> FilePath -> Int -> IO ()
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

mcts :: (Show a, Eq a, MCTS a) => RWST GenIO [(String, Diagram B)] (Z.TreePos Z.Full a) IO ()
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
          let (xs, d) = rollout (rootLabel t) (even depth)
              (nodes, weights) = unzip xs
          when (not (null xs)) $ do
            modify (Z.modifyTree (\x -> x{subForest = map (\n -> Node n []) nodes}))
            i <- ask >>= liftIO . categorical (V.fromList weights)
            -- print diagram
            dt <- gets (drawMCTSTree (nodes !! i) . Z.toTree)
            tell [(printf "A%03d" depth, vsep 1 [d, dt])]
            modify (fromJust . Z.childAt i)
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

-- select till no children
-- @no children, set vL, run simulate
-- end of simulate, set zL
-- on unwind set for each node V(sL), N, etc
-- mcts :: Game g => Tree g -> IO [Tree (MCTS g)]

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
    in (xs, d)

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

data AlphaGoStyle = AlphaGoStyle
  {
    prior :: Double
  , pred :: Double
  }

-- drawInfo :: Game g => Info g -> Diagram B
-- drawInfo x =
--   where n = text $ "N=" ++ show (visitCount x)
--         p = text $ "P=" ++ show (priorProb x)

-- we pick the node that is visited the most number of times. Because
-- nodes are picked by maximizing the action value + prior. Suppose
-- there is no prior and the action value is purely based on zL, then
-- this reduces to picking the move that maximizes the number of wins.

-- data Phase = Selection | Expansion | Evaluation | Backup

-- type GameTree st = Tree (Info st)

-- minimax :: 

-- Each node of the tree should display:
-- 1. N = count
-- 2. prior = value
-- 3. Q

-- During a simulation, render the following
-- 1. iter = count
-- 2. highlight leaf node
-- 3. zL = undefined till reach the end
-- 4. vL = undefined till leaf reached

-- render :: Tree (Info st) -> 

-- play :: st ->

fullGameTree :: Game g => g -> Tree g
fullGameTree g = unfoldTree (\(g, player1) -> (g, map (, not player1) $ next g player1)) (g, True)

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

{-
How do you generate copies of the tree at each step?
The answer can only be with a zipper
-}

data MM g = MM
  {
    game :: g
  , best :: Int
  }

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

drawGameTree :: Game g => Tree g -> Diagram B
drawGameTree = renderTree draw (~~) . forceLayoutTree . symmLayout' (with & slHSep .~ 6 & slVSep .~ 3)

drawMMTree :: Game g => Tree (MM g) -> Diagram B
drawMMTree = renderTree f (~~) . symmLayout' (with & slHSep .~ 6 & slVSep .~ 5)
  where f x = (text (show (best x)) # fontSize (local 0.5) `atop` square 1 # fc cyan) === strutY 0.1 === draw (game x)

main :: IO ()
main = do
  let g = GreedyCoins [10,3,1,2,7] (0, 0)
  drawMCTS (UCT 0 0 0 g) 1000 1500 "/home/naren/Desktop/uct" 3
  -- renderRasterific "example.pdf" (dims2D 1000 1000) (drawMMTree . (!! 0) . minimax $ t)

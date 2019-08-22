{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Data.Tree
import Diagrams.Prelude
import Diagrams.Backend.Rasterific
import Diagrams.TwoD.Layout.Tree
import qualified Data.Tree.Zipper as Z
import Control.Monad (zipWithM)
import Control.Monad.RWS.Lazy hiding (local)
import Data.Maybe (fromJust)
import System.Random.MWC
import System.Random.MWC.Distributions (uniformShuffle)
import qualified Data.Vector as V

data GreedyCoins = GreedyCoins
  {
    board :: [Int]
  , total :: (Int, Int)
  }

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
    | otherwise = [g{board = tail (board g), total = playerScore (head (board g))},
                   g{board = init (board g), total = playerScore (last (board g))}]
    where playerScore x = if player1 then (a + x, b) else (a, b + x)
          (a, b) = total g
  scores = total

data Info g = Info
  {
    state :: g
  , visitCount :: Int
  , priorProb :: Double
  , actionValueSum :: Double
  }

-- drawInfo :: Game g => Info g -> Diagram B
-- drawInfo x =
--   where n = text $ "N=" ++ show (visitCount x)
--         p = text $ "P=" ++ show (priorProb x)

-- we pick the node that is visited the most number of times. Because
-- nodes are picked by maximizing the action value + prior. Suppose
-- there is no prior and the action value is purely based on zL, then
-- this reduces to picking the move that maximizes the number of wins.

data Phase = Selection | Expansion | Evaluation | Backup

type GameTree st = Tree (Info st)

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
          get >>= tell . (:[]) . Z.toTree . Z.root
          return s

drawGameTree :: Game g => Tree g -> Diagram B
drawGameTree = renderTree draw (~~) . forceLayoutTree . symmLayout' (with & slHSep .~ 6 & slVSep .~ 3)

drawMMTree :: Game g => Tree (MM g) -> Diagram B
drawMMTree = renderTree f (~~) . symmLayout' (with & slHSep .~ 6 & slVSep .~ 5)
  where f x = (text (show (best x)) # fontSize (local 0.5) `atop` square 1 # fc cyan) === strutY 0.1 === draw (game x)

main :: IO ()
main = do
  t <- randomGameTree $ GreedyCoins [10,3,1,2,7] (0, 0)
  renderRasterific "example.pdf" (dims2D 1000 1000) (drawMMTree . (!! 0) . minimax $ t)

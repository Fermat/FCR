module Cegt.Loop where
import Cegt.Syntax
import Cegt.Rewrite

import Data.List

getList :: Trace -> [Name]
getList (Trace ls) = map fst ls

findCycle :: [Name] -> [Name] -> ([Name], [Name])
findCycle [] pre = (pre, [])
findCycle (y:ys) pre = case findIndex (\x -> x == y) ys of
                          Nothing -> findCycle ys (pre++[y])
                          Just i ->  (pre, y : take i ys)

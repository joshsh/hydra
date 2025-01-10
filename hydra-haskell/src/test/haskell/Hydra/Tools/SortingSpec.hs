module Hydra.Tools.SortingSpec where

import qualified Test.Hspec as H

import Hydra.Tools.Sorting


checkSort :: [(Int, [Int])] -> Either [[Int]] [Int] -> H.Expectation
checkSort adj exp = H.shouldBe (topologicalSort adj) exp

checkSortSCC :: [(Int, [Int])] -> [[Int]] -> H.Expectation
checkSortSCC adj exp = H.shouldBe (topologicalSortComponents adj) exp

checkSortDiscreteSet :: H.SpecWith ()
checkSortDiscreteSet = H.describe "Check sorting of discrete sets (no dependencies)" $ do

  H.it "Empty set" $
    checkSort [] (Right [] :: Either [[Int]] [Int])

  H.it "Singleton set" $
    checkSort [(1, [])]
      (Right [1])

  H.it "Discrete set with multiple elements" $
    checkSort [(3, []), (1, []), (2, [])]
      (Right [3, 2, 1])

checkSortTreesAndDags :: H.SpecWith ()
checkSortTreesAndDags = H.describe "Check sorting of trees and DAGs" $ do

  H.it "Linked list" $
    checkSort [(3, [1]), (2, [3]), (1, [])]
      (Right [1, 3, 2])

  H.it "Binary tree" $
    checkSort [(3, [1, 4]), (4, [6, 2]), (1, [5]), (2, []), (6, []), (5, [])]
      (Right [6, 5, 2, 4, 1, 3])

  H.it "Two trees" $
    checkSort [(3, [1, 4]), (5, [6, 2]), (2, [7]), (1, []), (4, []), (6, []), (7, [])]
      (Right [7, 6, 4, 2, 5, 1, 3])

  H.it "Diamond (DAG)" $
    checkSort [(1, [3, 4]), (3, [2]), (4, [2]), (2, [5]), (5, [])]
      (Right [5, 2, 3, 4, 1])

checkSortCycles :: H.SpecWith ()
checkSortCycles = H.describe "Check that sorting of graphs with cycles fails" $ do

  H.it "Two-node cycle" $
    checkSort [(1, [2]), (2, [1])]
      (Left [[1, 2]])

  H.it "Cycle with incoming and outgoing edges" $
    checkSort [(1, [3]), (3, [2]), (2, [3, 4]), (4, [5]), (5, [])]
      (Left [[2, 3]])

checkSortSCCDiscreteSet :: H.SpecWith ()
checkSortSCCDiscreteSet = H.describe "Check sorting of discrete sets (no dependencies)" $ do

  H.it "Empty set" $
    checkSortSCC []
      ([] :: [[Int]])

  H.it "Singleton set" $
    checkSortSCC [(1, [])]
      [[1]]

  H.it "Discrete set with multiple elements" $
    checkSortSCC [(3, []), (1, []), (2, [])]
      [[3],[2],[1]]

checkSortSCCWeaklyConnectedComponents :: H.SpecWith ()
checkSortSCCWeaklyConnectedComponents = H.describe "Check weakly-connected components" $ do

  H.describe "Single, two-element component" $ do
    H.it "test #1" $
      checkSortSCC [(1, [2]), (2, [])]
        [[2], [1]]
    H.it "test #2" $
      checkSortSCC [(2, [1]), (1, [])]
        [[1], [2]]

  H.it "Multiple-element component" $ do
    checkSortSCC [(2, [1, 3]), (1, [3]), (3, [])]
      [[3], [1], [2]]

checkSortSCCStronglyConnectedComponents :: H.SpecWith ()
checkSortSCCStronglyConnectedComponents = H.describe "Check strongly-connected components" $ do

  H.describe "Cycle of two nodes" $ do
    H.it "test #1" $
      checkSortSCC [(1, [2]), (2, [1])]
        [[1, 2]]
    H.it "test #2" $
      checkSortSCC [(2, [1]), (1, [2])]
        [[1, 2]]

  H.describe "Cycle of three nodes, ordered naturally" $ do

    H.it "test #1" $
      checkSortSCC [(1, [2]), (2, [3]), (3, [1])]
        [[1, 2, 3]]
    H.it "test #2" $
      checkSortSCC [(2, [1]), (3, [2]), (1, [3])]
        [[1, 2, 3]]

  H.it "Multiple, disconnected cycles, each ordered naturally" $ do
    checkSortSCC
      ([(200, [])] ++ [(100, [])] ++ [(300, [])] ++ [(10, [20]), (20, [10])] ++ [(1, [2]), (2, [3]), (3, [1])])
      [[300], [200], [100], [10, 20], [1, 2, 3]]

  H.it "Complex cycles" $ do
    checkSortSCC [(1, [2, 3]), (2, [3]), (3, [1])]
      [[1, 2, 3]]

checkSortSCCMixed :: H.SpecWith ()
checkSortSCCMixed = H.describe "Check graphs which are a mix of weakly- and strongly-connected components" $ do

  H.it "Chain of three SCCs" $
    checkSortSCC
      [(1, [2, 10]), (2, [3]), (3, [1]), (10, [20]), (20, [100, 10]), (100, [])]
      [[100], [10, 20], [1, 2, 3]]

  H.it "SCCs with dependencies to/from non-SCC nodes" $
    checkSortSCC
      [(1, [2, 3, 10]), (2, [3]), (3, [1]),
       (10, [20, 30]), (20, [30]), (30, []),
       (100, [200, 2]), (200, []), (300, [100]),
       (1000, []),
       (2000, [])]
      [[2000], [1000], [200], [30], [20], [10], [1, 2, 3], [100], [300]]

spec :: H.Spec
spec = do
  H.describe "Check topological sort (without cycles)" $ do
    checkSortDiscreteSet
    checkSortTreesAndDags
    checkSortCycles

  H.describe "Check sorting of strongly connected components" $ do
    checkSortSCCDiscreteSet
    checkSortSCCWeaklyConnectedComponents
    checkSortSCCStronglyConnectedComponents
    checkSortSCCMixed

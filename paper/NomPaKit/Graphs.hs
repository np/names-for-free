{-# LANGUAGE QuasiQuotes #-}
{-# OPTIONS_GHC -F -pgmF frquotes #-}
{-# OPTIONS -Wall -fno-warn-missing-signatures -fno-warn-unused-imports #-}
module NomPaKit.Graphs (graphC, shiftG, addG, shiftGø, αG, protectedAddGraph,
                        protectedAddShiftGraph, unprotectedAddGraph,
                        shiftingVsAddingGraphs, consingGraph) where

import Data.Monoid
import Control.Arrow ((***))

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder.Math as M
import qualified Language.LaTeX.Builder.Color as C
import qualified Language.LaTeX.Builder.Babel as Babel
import qualified Language.LaTeX.Length as L

import NomPaKit (diagram)
import NomPaKit.Basics (array,put,(↦))
import NomPaKit.Verb (myHstring)
import NomPaKit.QQ (frTop, frAntiq, frQQ, defaultQQ, nodesQ)
import MiniTikz.Builder (oF, ofDist, left, above, right, nodeDistance, path, spath, dnode', scope)

map4 :: (a -> b) -> (a,a,a,a) -> (b,b,b,b)
map4 f (a,b,c,d) = (f a, f b, f c, f d)

type Nodes a = [(a, a, a, a)]
type Links = [(Int,Int)]

-- World graphs
graph :: LatexItem -> Nodes LatexItem -> Links -> ParItemW
graph graphLabel nodes links = B.center !$? do -- this center covers the label as well
  diagram
    [scope [nodeDistance "0.5cm"] $
      (concat $
        zipWith (\k (l, lb, rb, r) ->
                  [n (ln k)  [[above]`oF`(ln (k-1)) | k > 0]                    lb
                  ,n (lnt k) [[left]`oF`(ln k),(left,"-0.5cm")`ofDist`(ln k)]   l
                  ,n (rn k)  [[right]`oF`(ln k),(right,"1cm")`ofDist`(ln k)]    rb
                  ,n (rnt k) [[right]`oF`(rn k),(right,"-0.5cm")`ofDist`(rn k)] r])
        [0..] (reverse nodes)) ++ map (uncurry link) links
    ]
  put $ B.para graphLabel
 where
   pa style src dst pos opts lbl = spath style src pos opts lbl dst
   n ident opts lbl = dnode' ident opts lbl []
   ln k = show (k :: Int) ++ "L"
   rn k = show (k :: Int) ++ "R"
   lnt k = ln k ++ "T"
   rnt k = rn k ++ "T"
   link l r = pa "-" (ln l) (rn r) above [] ø

graphC lbl edges = graph lbl (map (\k-> map4 myHstring (show k, "●", "●", show k)) (reverse [0..size-1])) edges
  where size = maximum (map (uncurry max) edges) + 1

shiftGø k = map (\x -> (x, x)) [0..k-1]
addG k = map ((k+) *** (k+))
shiftG k g = addG k g ++ shiftGø k
consG b1 b2 g = (b1, b2) : filter (\(x1,x2) -> not (x1 == b1 || x2 == b2)) g
αG :: [(Int,Int)]
αG = [(0, 3), (3, 0), (2, 2)]

protectedAddGraph = graph ø
  [nodesQ|
  |        ●   ⋮
  |        ●   2+k+ℓ
  |⋮   ●   ●   1+k+ℓ
  |2+ℓ ●   ●   k+ℓ
  |1+ℓ ●        
  |ℓ   ●        
  |ℓ∸1 ●   ●   ℓ∸1
  |⋮   ●   ●   ⋮
  |2   ●   ●   2
  |1   ●   ●   1
  |0   ●   ●   0
  |]
  [8 ↦ 10
  ,7 ↦ 9
  ,6 ↦ 8
  ,5 ↦ 7
  ,4 ↦ 4
  ,3 ↦ 3
  ,2 ↦ 2
  ,1 ↦ 1
  ,0 ↦ 0]

protectedAddShiftGraph = graph ø
  [nodesQ|
  |        ●   ⋮
  |        ●   2+k+ℓ
  |⋮   ●   ●   1+k+ℓ
  |2+ℓ ●   ●   k+ℓ
  |1+ℓ ●   ●    
  |ℓ   ●   ●    
  |ℓ∸1 ●   ●   ℓ∸1
  |⋮   ●   ●   ⋮
  |2   ●   ●   2
  |1   ●   ●   1
  |0   ●   ●   0
  |]
  [8 ↦ 10
  ,7 ↦ 9
  ,6 ↦ 8
  ,5 ↦ 7
  ,4 ↦ 4
  ,3 ↦ 3
  ,2 ↦ 2
  ,1 ↦ 1
  ,0 ↦ 0]

unprotectedAddGraph = graph ø
  [nodesQ|
  |        ●   ⋮
  |        ●   2+k+ℓ
  |⋮   ●   ●   1+k+ℓ
  |2+ℓ ●   ●   k+ℓ
  |1+ℓ ●   ●   k+ℓ∸1
  |ℓ   ●   ●   ⋮
  |ℓ∸1 ●   ●   2+k
  |⋮   ●   ●   1+k
  |2   ●   ●   k
  |1   ●   ●   ⋮
  |0   ●   ●   0
  |]
  [8 ↦ 10
  ,7 ↦ 9
  ,6 ↦ 8
  ,5 ↦ 7
  ,4 ↦ 6
  ,3 ↦ 5
  ,2 ↦ 4
  ,1 ↦ 3
  ,0 ↦ 2]

shiftingVsAddingGraphs =
  array 4
    [graphC «{|αᵣ|}» αG
    ,graphC «{|αᵣ ⟦+1⟧|}» (addG 1 αG)
    ,graphC «{|αᵣ ⟦↑1⟧|}» (shiftG 1 αG)
    ]

consingGraph =
  array 4
    [graphC «{|αᵣ|}» αG
    ,graphC «{|⟨4,2⟩⟦◅⟧ αᵣ|}» (consG 4 2 αG)
    ,graphC «{|⟨4,4⟩⟦◅⟧ ⟨4,2⟩⟦◅⟧ αᵣ|}» (consG 4 4 (consG 4 2 αG))
    ]

{-# LANGUAGE EmptyDataDecls #-}
module MiniTikz.Types where

import Data.Monoid
import qualified Data.Tree as T

data Posi = NamedPosi String

type Angle = Int

data Dir = NamedDir String
         | Angle Angle

data Coord = CoordCanvas Rational Rational -- as in “(0,1)”
           | CoordCanvasPolar Angle Rational  -- as in “(90:1)”
           | CoordNode String
           -- Explicit CoordSystem [(String,String)] -- “<coordinate system> cs:<key-value-pair>*”

data EdgeOpt = Bend Posi

data PathOpt a = Fill a
               | RawPathOpt String

data Path a = Concat [Path a]
            | Group (Path a)              -- as in “'{' <path> '}'”
            | PathOpts [PathOpt a]        -- as in “'[' <path-opt>* ']'”
            | MoveTo Coord                -- as in “<coordinate>”
            | LineTo Coord                -- as in “'--' <coordinate>”
            | FirstHorizThenVert Coord    -- as in “'-|' <coordinate>”
            | FirstVertThenHoriz Coord    -- as in “'|-' <coordinate>”
            | CurveTo Coord (Maybe Coord) Coord -- as in “'..' 'controls' <coordinate> ['and' <coordinate>] '..' <coordinate>”
            | Cycle                       -- as in “'--' 'cycle'”
            | Rectangle Coord             -- as in “'rectangle' <coordinate>”
            -- starting from page 142: circle, ellipse, arc, grid, parabola, sin, cos, svg, plot
            | To
            -- is "let" really usefull in the target language?
            | PNode (Node a)
            | Edge [EdgeOpt] [Node a] Coord -- as in “'edge' '[' <options> ']' <nodes> <coordinate>”

instance Monoid (Path a) where
  mconcat = Concat
  mappend x y = mconcat [x,y]
  mempty = mconcat []

type NodeId = String

type Dist = String

data ScopeOpt = ScopeOpt String String
              | Grow Dir
              -- | LevelStyle Int [ScopeOpt]

data NodeOpt = Posi Posi
             | Of [Posi] NodeId
             | OfDist Posi Dist NodeId
             | NodeStyle String
             | NodeScopeOpt ScopeOpt

data VoidForeach -- TODO

data ChildOpt -- TODO

type Child a = a
{-
data Child a = Child { childOpts    :: [ChildOpt]
                     , childForeach :: Maybe VoidForeach
                     , childLabel   :: a }
-}

data Node a = Node { nodeId       :: NodeId
                   , nodeOpts     :: [NodeOpt]
                   , nodeLabel    :: a
                   , nodeChildren :: T.Forest (Child a)
                   }

type Mat a = [[a]]

data Decl a = Path (Path a)
            | Scope [ScopeOpt] [Decl a]
            | Matrix (Mat a)

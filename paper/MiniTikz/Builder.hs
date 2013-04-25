module MiniTikz.Builder
  (Posi,Angle,Dir,Coord,EdgeOpt,PathOpt,Path,NodeId,Dist,ScopeOpt
  ,NodeOpt,ChildOpt,Child,Node,Mat,Decl
  ,(.--)
  ,(.-|)
  ,(.|-)
  ,spath
  ,child
  ,schild
  ,node
  ,snode
  ,pnode
  ,pnode'
  ,path
  ,dnode
  ,dnode'
  ,scope
  ,matrix
  ,nodeDistance
  ,levelDistance
  ,siblingDistance
  ,levelStyle
  ,down
  ,up
  ,north
  ,south
  ,east
  ,west
  ,northEast
  ,northWest
  ,southEast
  ,southWest
  ,above
  ,below
  ,angle
  ,rawScopeOpt
  ,oF
  ,ofDist
  ,nodeStyle
  ,nodeScopeOpt
  ,bend
  ,left
  ,right
  ,grow
  ,coordCanvas
  ,coordNode
  ,fill
  ,thick
  ,ultrathick
  ,linewidth
  ,pathOpts
  ,draw
  ,moveTo
  ,(.→.)
  ,(.←.)
  ,group
  )
where

import MiniTikz.Types
import qualified Data.Tree as T

rawPathOpt :: String -> PathOpt a
rawPathOpt = RawPathOpt

fill :: a -> PathOpt a
fill = Fill

draw, thick, ultrathick, (.→.), (.←.) :: PathOpt a
draw = rawPathOpt "draw"
thick = rawPathOpt "thick"
ultrathick = rawPathOpt "ultra thick"
(.→.) = rawPathOpt "->"
(.←.) = rawPathOpt "<-"
linewidth :: String -> PathOpt a
linewidth s = rawPathOpt ("line width=" ++ s)

coordCanvas :: Rational -> Rational -> Coord
coordCanvas = CoordCanvas

coordNode :: NodeId -> Coord
coordNode = CoordNode

moveTo :: Coord -> Path a
moveTo = MoveTo

infixl 5 .--
infixl 5 .-|
infixl 5 .|-

(.--) :: Path a -> Coord -> Path a
(.--) p c = Concat[p, LineTo c]

(.-|) :: Path a -> Coord -> Path a
(.-|) p c = Concat[p, FirstHorizThenVert c]

(.|-) :: Path a -> Coord -> Path a
(.|-) p c = Concat[p, FirstVertThenHoriz c]

spath :: String -> NodeId -> Posi -> [EdgeOpt] -> a -> NodeId -> Decl a
spath pathStyle pathSrc pathPos pathEdgeOpts pathLabel pathDst =
  Path $ Concat
  [pathOpts[rawPathOpt pathStyle]
  ,moveTo (coordNode pathSrc)
  ,Edge pathEdgeOpts [node "" [Posi pathPos] pathLabel []] (coordNode pathDst)
  ]

child :: [ChildOpt] -> Maybe VoidForeach -> a -> Child a
child _ _ x = x -- Child

schild :: a -> Child a
schild = child [] Nothing

node :: NodeId -> [NodeOpt] -> a -> T.Forest (Child a) -> Node a
node = Node

snode :: NodeId -> [NodeOpt] -> a -> T.Forest a -> Node a
snode n opts lbl = node n opts lbl . (fmap . fmap) schild

pnode :: Node a -> Path a
pnode = PNode

pnode' :: NodeId -> [NodeOpt] -> a -> T.Forest (Child a) -> Path a
pnode' n os x ts = pnode (snode n os x ts)

group :: Path a -> Path a
group = Group

pathOpts :: [PathOpt a] -> Path a
pathOpts = PathOpts

path :: Path a -> Decl a
path = Path

dnode :: Node a -> Decl a
dnode = path . pnode

dnode' :: NodeId -> [NodeOpt] -> a -> T.Forest (Child a) -> Decl a
dnode' n ns x f = dnode (node n ns x f)

scope :: [ScopeOpt] -> [Decl a] -> Decl a
scope = Scope

matrix :: Mat a -> Decl a
matrix = Matrix

-- draw = path [draw]

nodeDistance, levelDistance, siblingDistance :: Dist -> ScopeOpt
nodeDistance = ScopeOpt "node distance"
levelDistance = ScopeOpt "level distance"
siblingDistance = ScopeOpt "sibling distance"

levelStyle :: Int -> [ScopeOpt] -> ScopeOpt
-- levelStyle = LevelStyle
levelStyle i [ScopeOpt "sibling distance" opt] =
  rawScopeOpt ("level "++show i++"/.style") ("{sibling distance="++opt++"}")
levelStyle _ _ = error "levelStyle: unsupported yet"

class HasGrow a where grow :: Dir -> a

instance HasGrow ScopeOpt where grow = Grow
instance HasGrow NodeOpt  where grow = NodeScopeOpt . grow

class HasLeftRight a where
  left  :: a
  right :: a

instance HasLeftRight Dir where
  left  = NamedDir "left"
  right = NamedDir "right"

instance HasLeftRight Posi where
  left  = NamedPosi "left"
  right = NamedPosi "right"

down, up, north, south, east, west, northEast, northWest,
  southEast, southWest :: Dir

down      = NamedDir "down"
up        = NamedDir "up"
north     = NamedDir "north"
south     = NamedDir "south"
east      = NamedDir "east"
west      = NamedDir "west"
northEast = NamedDir "north east"
northWest = NamedDir "north west"
southEast = NamedDir "south east"
southWest = NamedDir "south west"

above, below :: Posi
above = NamedPosi "above"
below = NamedPosi "below"

angle :: Int -> Dir
angle n | n >= 0 && n <= 360 = Angle n
        | otherwise          = error $ "angle: out of range: " ++ show n

rawScopeOpt :: String -> String -> ScopeOpt
rawScopeOpt = ScopeOpt

oF :: [Posi] -> NodeId -> NodeOpt
oF = Of

ofDist :: (Posi,Dist) -> NodeId -> NodeOpt
ofDist (p,d) n = OfDist p d n

nodeStyle :: String -> NodeOpt
nodeStyle = NodeStyle

nodeScopeOpt :: ScopeOpt -> NodeOpt
nodeScopeOpt = NodeScopeOpt

bend :: Posi -> EdgeOpt
bend = Bend

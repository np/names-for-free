{-# LANGUAGE QuasiQuotes, RankNTypes #-}
module MiniTikz.Diagram where

import MiniTikz.Types
import Data.List (intersperse, sortBy)
import Data.Ord
import qualified Data.Tree as T
import Language.LaTeX
import qualified Language.LaTeX.Builder.Internal as BI
import qualified Language.LaTeX.Builder as B
import Language.LaTeX.Builder.QQ

completeMat :: a -> [[a]] -> [[a]]
completeMat dflt rows =
  map (take (maximum (map length rows)) . (++repeat dflt)) rows

mc :: Monoid a => [a] -> a
mc = mconcat

tikzpicture :: [ScopeOpt] -> ParItem -> ParItem
tikzpicture opts = BI.parEnv "tikzpicture"
  [BI.namedOpts (map (fmap BI.rawAnyTex . scopeOpt) opts)] . BI.parItem

scopeOpt :: ScopeOpt -> Named String
scopeOpt (ScopeOpt name val) = BI.named name val
scopeOpt (Grow d)            = BI.named ø ("grow " ⊕ onDir d)
{-
scopeOpt (LevelStyle l opts) = BI.named ø ("level " ⊕ show l ⊕ "/.style") ("{" ⊕ mc (scopeOpt ⊕"}"  onDir d)
-}

onDir :: Dir -> String
onDir (NamedDir s) = s
onDir (Angle i)    = show i

diagram :: [ScopeOpt] -> [Decl LatexItem] -> ParItem
diagram diagOpts = tikzpicture diagOpts . B.para . onDecls

parenArg :: forall m. [Char] -> Arg m
parenArg = BI.rawArg . ('(':) . (⊕")")

-- no at(...) support
onPathOp :: Path LatexItem -> [Arg LatexItem]
onPathOp (Concat ps) = mconcat $ fmap onPathOp ps
onPathOp (Group p)   = BI.rawArg " { " : onPathOp p ⊕ [BI.rawArg " }"]
onPathOp (PathOpts opts) = [BI.namedOpts $ fmap onPathOpt opts]
onPathOp (MoveTo c)      = [BI.rawArg " ", onCoord c]
onPathOp (LineTo c)      = [BI.rawArg " -- ", onCoord c]
onPathOp (FirstHorizThenVert c) = [BI.rawArg " -| ", onCoord c]
onPathOp (FirstVertThenHoriz c) = [BI.rawArg " |- ", onCoord c]
onPathOp (CurveTo _ _ _) = error "onPathOp: CurveTo"
onPathOp Cycle           = [BI.rawArg " --cycle "]
onPathOp (Rectangle c)   = [BI.rawArg " rectangle ", onCoord c]
onPathOp To              = error "onPathOp: To"
onPathOp (PNode n)       = onNode n
onPathOp (Edge opts nodes c) =
                      [BI.rawArg " edge"
                      ,BI.namedOpts (map edgeOpt opts)] ⊕
                      mconcat (map onNode nodes) ⊕
                      [onCoord c]

onPath :: Path LatexItem -> LatexItem
onPath p = BI.latexCmdArgs "path" $ onPathOp p ⊕ [semiArg]

onPathOpt :: PathOpt LatexItem -> Named LatexItem
onPathOpt (RawPathOpt x) = BI.named ø (BI.rawTex x)
onPathOpt (Fill x) = BI.named "fill" x

onCoord :: MiniTikz.Types.Coord -> Arg LatexItem
onCoord (CoordCanvas x y) = BI.liftArg $ mc[BI.rawTex "("
                                           ,BI.latexCast (B.rat x)
                                           ,BI.rawTex ","
                                           ,BI.latexCast (B.rat y)
                                           ,BI.rawTex ")"]
onCoord (CoordNode n)     = nodeArg n
onCoord _ = error "onCoord"

semiArg :: forall m. Arg m
semiArg = BI.rawArg ";\n"

onPos :: Posi -> String
onPos (NamedPosi s) = s

spaced :: (a -> String) -> [a] -> String
spaced f = mc . intersperse " " . map f

onNodeIdent :: String -> LatexItem
onNodeIdent = BI.rawTex

edgeOpt :: EdgeOpt -> Named LatexItem
edgeOpt (Bend pos) = BI.named ø (BI.rawTex $ "bend " ⊕ onPos pos)

-- Doc PGF: 16.5.3
-- Beware: we use the positioning tikz library, which redefines these
nodeOpt :: NodeOpt -> Named LatexItem
nodeOpt (Posi pos) = BI.named ø (BI.rawTex $ onPos pos)
nodeOpt (Of poss nod) = BI.named (spaced onPos poss ⊕ " of") (onNodeIdent nod)
nodeOpt (OfDist pos dist nod) = BI.named (onPos pos) (BI.rawTex dist ⊕ [tex| of |] ⊕ onNodeIdent nod)
nodeOpt (NodeStyle style) = BI.named ø (BI.rawTex style)
nodeOpt (NodeScopeOpt opt) = fmap BI.rawTex $ scopeOpt opt

nodeArg :: [Char] -> Arg a
nodeArg "" = BI.noArg
nodeArg x  = parenArg x

onRow :: [LatexItem] -> LatexItem
onRow row = mc (intersperse [tex| & |] row) ⊕ [tex| \\ |]

onNode :: Node LatexItem -> [Arg LatexItem]
onNode (Node ident opts label children) =
  [BI.rawArg " node "
  ,nodeArg ident
  ,BI.namedOpts (map nodeOpt opts)
  ,BI.mandatory label
  ,BI.liftArg (onChildren children)]

onChildren :: [T.Tree LatexItem] -> LatexItem
onChildren [] = ø
onChildren xs = mc . map onTree $ xs

onTree :: T.Tree LatexItem -> LatexItem
onTree (T.Node x children) =
  [tex| child { node {|] ⊕ x ⊕ [tex|} |] ⊕
  onChildren children ⊕ [tex| }
|]

onMat :: [[LatexItem]] -> LatexItem
onMat mat =
  [tex|\matrix (m) [matrix of math nodes, row sep=1em, column sep=1em, text height=1.5ex, text depth=0.25ex] { |]
  ⊕ mc (map onRow mat) ⊕
  [tex| };|]

onDecl :: Decl LatexItem -> LatexItem
onDecl (Path pa) = onPath pa
onDecl (Matrix mat) = onMat mat
onDecl (Scope opts decls) =
  BI.latexCmdArgs "begin" [BI.mandatory [tex|scope|], BI.namedOpts (map (fmap BI.rawTex . scopeOpt) opts)] ⊕
  onDecls decls ⊕
  BI.latexCmdArgs "end" [BI.mandatory [tex|scope|]]

onDecls :: [Decl LatexItem] -> LatexItem
onDecls = mc . map onDecl . sortBy (comparing criterion)
      where criterion (Path PNode{}) = False -- some nodes first
            criterion _              = True

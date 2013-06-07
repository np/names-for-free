module Kit.ACM where

import Data.Maybe
import Data.Functor
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI

cat a1 a2 a3 = BI.parCmdArgs "category" $ map (BI.mandatory . BI.latexItem) [a1,a2,a3]

authorinfo (name, email', inst') =
  BI.preambleCmdArgs "authorinfo" $ map (BI.mandatory . BI.latexItem) [name, inst', email']

sigplanconf msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "sigplanconf") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args

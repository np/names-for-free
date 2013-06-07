module Kit.IEEE where

import Data.Maybe
import Data.Functor
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI

ieee msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "IEEEtran") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args

inst = BI.latexCmdArg "inst"
email = BI.latexCmdArg "email"

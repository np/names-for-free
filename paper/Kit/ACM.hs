module Kit.ACM where

import Data.Maybe
import Data.Functor
import Data.String
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Internal as BI

cat a1 a2 a3 = BI.parCmdArgs "category" $ map (BI.mandatory . BI.latexItem) [a1,a2,a3]

authorinfo (name, email', inst') =
  BI.preambleCmdArgs "authorinfo" $ map (BI.mandatory . BI.latexItem) [name, inst', email']

permission s =
  BI.preambleCmdArgs "permission" $ map (BI.mandatory . BI.latexItem) [s]

toappear s =
  BI.preambleCmdArgs "toappear" $ map (BI.mandatory . BI.latexItem) [s]

conferenceinfo confname confinfo =
  BI.preambleCmdArgs "conferenceinfo" $ map (BI.mandatory . BI.latexItem) [confname, confinfo]

copyrightyear i =
  BI.preambleCmdArgs "copyrightyear" $ map (BI.mandatory . BI.latexItem) [fromString (show (i :: Int))]

copyrightdata s =
  BI.preambleCmdArgs "copyrightdata" $ map (BI.mandatory . BI.latexItem) [s]

doi s =
  BI.preambleCmdArgs "doi" $ map (BI.mandatory . BI.latexItem) [s]

exclusivelicense    = BI.preambleCmdArgs "exclusivelicense" []
permissiontopublish = BI.preambleCmdArgs "permissiontopublish" []

authorversion copydata confname confinfo doi =
  BI.preambleCmdArgs "authorversion" $ map (BI.mandatory . BI.latexItem)
    [copydata, confname, confinfo, doi]

sigplanconf msize mpaper args =
  B.documentclass (BI.otherDocumentClassKind "sigplanconf") $
     maybeToList (BI.latexPaper <$> mpaper) ++
     maybeToList (BI.texLength <$> msize) ++
     args

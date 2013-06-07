module Kit.Config where

data Config = Config { displayNotes
                     , sloppyErrors
                     , sloppyAligns
                     , doCheckTypos
                     , colorful
                     , typesetErrors :: Bool }

config, final, draft :: Config
final = Config { displayNotes  = False
               , sloppyErrors  = True
               , sloppyAligns  = False
               , doCheckTypos  = True
               , colorful      = True
               , typesetErrors = False
               }
draft = final { displayNotes = True, doCheckTypos = False, typesetErrors = True }

-- CONFIG HERE
config = draft

noColors :: Config -> Bool
noColors = not . colorful

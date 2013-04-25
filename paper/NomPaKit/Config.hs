module NomPaKit.Config where

data Config = Config { displayNotes
                     , sloppyErrors
                     , sloppyAligns
                     , doCheckTypos
                     , colorful     :: Bool }

config, final, draft :: Config
final = Config { displayNotes = False
               , sloppyErrors = True
               , sloppyAligns = False
               , doCheckTypos = True
               , colorful     = True
               }
draft = final { displayNotes = True, doCheckTypos = False }

-- CONFIG HERE
config = draft

noColors :: Config -> Bool
noColors = not . colorful

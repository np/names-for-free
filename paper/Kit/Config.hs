module Kit.Config where

data Config = Config { displayNotes
                     , sloppyErrors
                     , sloppyAligns
                     , doCheckTypos
                     , colorful
                     , typesetErrors
                     , sparseSections :: Bool }

config, final, draft :: Config
final = Config { displayNotes   = False
               , sloppyErrors   = True
               , sloppyAligns   = False
               , doCheckTypos   = True
               , colorful       = True
               , typesetErrors  = False
               , sparseSections = False
               }
draft = final { displayNotes = True, doCheckTypos = False, typesetErrors = True }
diff  = final { colorful = False, sparseSections = True }

-- CONFIG HERE
config = draft

noColors :: Config -> Bool
noColors = not . colorful

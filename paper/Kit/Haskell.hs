module Kit.Haskell where

haskellify :: String -> String
haskellify = concatMap θ
  where θ '☐' = " "
        θ ' ' = " "
        θ 'λ' = "\\"
        θ '∈' = ":∈"
        θ '⊆' = ":⊆"
        θ '▹' = ":▹"
        θ '‼' = ""
        θ  x  = [x]

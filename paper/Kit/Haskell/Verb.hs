module Kit.Haskell.Verb (haskellCode,haskellCodeP) where

import Prelude
import Data.List
import Data.List.Split
import Data.Char
import Data.Functor

import Text.Highlighting.Kate

import Language.LaTeX
import qualified Language.LaTeX.Builder as B
import qualified Language.LaTeX.Builder.Color as C

import Kit.Basics
import Kit.Config
import Kit.Verb

nlTok :: Token
nlTok = (NormalTok, "\n")

unlineS :: [SourceLine] -> [Token]
unlineS = intercalate [nlTok]

highlightAsHaskell :: String -> [SourceLine]
highlightAsHaskell = highlightAs "haskell"

typeList = ["Nat","Maybe","Value","No","Binder","World","Empty","Name","Succ","Zero","Bool"
           ,"Insert","LC","Monoid","Monad","Functor","Fin","Leq","Either","Traversable"
           ,"Foldable","S","Eq","Applicative","Int"]

isUpperIdent :: String -> Bool
isUpperIdent []        = False
isUpperIdent ('`':x:_) = isUpper x
isUpperIdent (x:_)     = isUpper x

overrideStyle :: String -> TokenType -> TokenType
overrideStyle s tok
  | any (`isPrefixOf` s) ["Tm"]    || -- Tm, TmB, TmF...
    any (`isSuffixOf` s) ["Scope"] || -- SuccScope, UnivScope...
    s `elem` typeList
    = NormalTok
  -- * parenthesis seems to not be well separated out
  -- * no effect: fresh, in, ','
  | s `elem` ["→","←","∀","∃","λ","=","⇒","|",".",",","∇","fresh","in","≡","@","(",")","::","()","[","]","[]","≢"]
    = KeywordTok
  | tok `elem` [KeywordTok,OtherTok] && isUpperIdent s = DataTypeTok
overrideStyle _ tok = tok

tokenize :: TokenType -> String -> [String]
tokenize CommentTok = return
tokenize StringTok  = return
tokenize _          = split $ whenElt (`elem`"  ()[]λ")

{-
overrideSplits (c, 'λ':x) = [(KeywordTok,"λ"),(c,x)]
{-
overrideSplits (c, '(':x) = [(KeywordTok,"("),(c,x)]
-}
overrideSplits (c, xs)
  | "::" `isSuffixOf` xs   = [(c,init (init xs)),(KeywordTok,"::")]
--  | ")" `isSuffixOf` xs   = [(c,init xs),(KeywordTok,")")]
overrideSplits p          = [p]
-}
overrideSplits (c, xs) = ((,)c) <$> tokenize c xs

haskellCode :: Bool -> Bool -> Bool -> Bool -> String -> LatexItem
haskellCode wordBreakable mayAlign finalNewLine doKillNbsp
    = mc . map skipSpaces
         . concatMap overrideSplits
         . fnl
         . unlineS
         . highlightAsHaskell
         . killNbsp
  where skipSpaces (c, xs)
          | wordBreakable && all (`elem` " \n") xs = B.space
          | otherwise
              = stylize (overrideStyle xs c) $ verb mayAlign wordBreakable xs
        fnl | finalNewLine = (++[nlTok])
            | otherwise    = id
        killNbsp
          | doKillNbsp = map killNbspMap
          | otherwise  = id
        killNbspMap ' ' = ' '
        killNbspMap  x  =  x

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

haskellCodeP :: Bool -> Bool -> String -> ParItemW
haskellCodeP = qqP (haskellCode False True True False) haskellify

rgb :: Int -> Int -> Int -> C.Color
rgb r g b = C.rgb (f r) (f g) (f b)
  where f y = fromIntegral y / (2 ^ (16 :: Integer))

darkOrange3, firebrick, purple, gray25, mediumBlue :: C.Color
darkOrange3 = C.cmyk 0 0.65 0.99 0
firebrick = rgb 0xB2B2 0x2222 0x2222
purple = rgb 0xA0A0 0x2020 0xF0F0
gray25 = rgb 0x4040 0x4040 0x4040
mediumBlue = rgb 0x0000 0x0000 0xCDCD

color = mapNonEmpty . C.textcolor

stylize :: TokenType -> (LatexItem -> LatexItem)
stylize tok
  | colorful config =
    case tok of
      KeywordTok  -> color darkOrange3

      StringTok   -> color firebrick
      CharTok     -> color firebrick
      DecValTok   -> color firebrick
      FloatTok    -> color firebrick
      DataTypeTok -> color firebrick

      FunctionTok -> color mediumBlue
      NormalTok   -> color mediumBlue
      OtherTok    -> color mediumBlue

      CommentTok  -> color purple
      ErrorTok
        | sloppyErrors config -> color C.red
        | otherwise           -> error "Kit.Haskell.Verb: turn on Kit.Config.sloppyErrors and check the document for errors (red)"
      _           -> C.textcolor C.green
  | otherwise = id

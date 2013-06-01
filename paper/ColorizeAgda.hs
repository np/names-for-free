{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS -fno-warn-orphans #-}
module ColorizeAgda
  (module ColorizeAgda
  ,Token(..), ParseError) where

import Data.Functor
import Data.List
import Data.Int
import Data.Ratio
-- import Agda.Syntax.Position (Position(..), Interval'(..), Range'(..), Interval, Range, getRange, posPos)
import Agda.Syntax.Position (Position(..), Interval(..), Range(..), getRange)
import Agda.Syntax.Parser.Lexer (lexer, normal)
import Agda.Syntax.Parser.Tokens (Token(..))
import Agda.Syntax.Parser.Monad (ParseError, ParseResult(..),
                                 ParseFlags(..), parse)
import Language.Haskell.TH (appE, varE, conE)
import Language.Haskell.TH.Syntax (Lift(lift))

instance (Integral a, Lift a) => Lift (Ratio a) where
  lift r = varE '(%) `appE` lift (numerator r) `appE` lift (denominator r)

data Color = RGB {red, green, blue :: Int}
           | CMYK {cyan, magenta, yellow, black :: Rational}
  deriving (Show)

instance Lift Color where
  lift (RGB r g b) = conE 'RGB `appE` lift r `appE` lift g `appE` lift b
  lift (CMYK c m' y k) = conE 'CMYK `appE` lift c `appE` lift m' `appE` lift y `appE` lift k

darkOrange3, firebrick, purple, gray25, mediumBlue :: Color
-- darkOrange3 = RGB 0xCDCD 0x6666 0x0000
darkOrange3 = CMYK 0 0.65 0.99 0
firebrick = RGB 0xB2B2 0x2222 0x2222
purple = RGB 0xA0A0 0x2020 0xF0F0
gray25 = RGB 0x4040 0x4040 0x4040
mediumBlue = RGB 0x0000 0x0000 0xCDCD

zipInfo :: String -> [((Int32, Int32), a)] -> [(String, Maybe a)]
zipInfo = go 0
 where
  add s i | null s    = id
          | otherwise = ((s,i):)
  go _   s [] = add s Nothing []
  go cur s (((start , stop), info) : is) =
    add pre Nothing . add mid (Just info) $ go (stop - 1) post is
   where
    (pre, midpost) = genericSplitAt (start - 1 - cur) s
    (mid, post) = genericSplitAt (stop - start) midpost

defaultColor :: Token -> Maybe Color
defaultColor TokKeyword{} = Just darkOrange3
defaultColor TokString{} = Just purple -- seems to be not triggered
defaultColor TokLiteral{} = Just purple
defaultColor TokSymbol{} = Just darkOrange3 -- Just gray25
defaultColor TokSetN{} = Just mediumBlue
defaultColor TokComment{} = Just firebrick
defaultColor TokId{} = Just mediumBlue
defaultColor TokQId{} = Just mediumBlue
{-
defaultColor TokTeX{}
defaultColor TokDummy
defaultColor TokEOF
-}
defaultColor _            = Nothing

colorizeAgda :: String -> Either ParseError [(String, Maybe Token)]
colorizeAgda input
    = fmap (zipInfo input . map addInterval)
    . fromParseResult
    . parse flags [normal] parser
    $ input
  where
    flags = ParseFlags{parseKeepComments=True}
    parser = lexer withToken
    withToken TokEOF = return []
    withToken tok    = (tok:) <$> parser
    getInterval (Range []) = error "getInterval: empty"
    getInterval (Range is) = (posPos . iStart . head $ is, posPos . iEnd . last $ is)
    addInterval x = (getInterval (getRange x), x)
    fromParseResult (ParseOk _ x)   = Right x
    fromParseResult (ParseFailed e) = Left e

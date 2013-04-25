{-# LANGUAGE TypeFamilies, GeneralizedNewtypeDeriving, RankNTypes, EmptyDataDecls #-}
{-# OPTIONS -Wall #-}
module NomPaKit.DSL where

import Control.Applicative hiding ((<$>))
import Data.Tree
import qualified Text.PrettyPrint.Leijen as P
import Text.PrettyPrint.Leijen ((<$>), (<+>), Pretty(..), Doc)
import NomPaKit.Basics

node :: a -> Forest a -> Tree a
node = Node

str :: String -> Tree String
str s = node s []

int :: Integral a => a -> Tree String
int = str . show . toInteger

type ℕ = Integer
-- type Interactive = IO ()
newtype Interactive = Interactive { runInteractive :: [String] }

class LIT r where
  num   :: ℕ -> r ℕ
  text  :: String -> r String
  list  :: [r a] -> r [a]
  nodeT :: r a -> r [Tree a] -> r (Tree a)

class LIT r => OPS r where
  (*:),(+:),(∸),(÷) :: r ℕ -> r ℕ -> r ℕ
  (++:) :: r String -> r String -> r String
  showT :: r ℕ -> r String
  printT :: r String -> r Interactive
  (>>:) :: r Interactive -> r Interactive -> r Interactive

class LET r where
  letH :: String -> r a -> (r a -> r b) -> r b

class LAM r where
  lam :: String -> (r a -> r b) -> r (a -> b)

infixl 4 `app`
class APP r where
  app :: r (a -> b) -> r a -> r b

class LIT r => CON r where
  con0 :: String -> r a
  con1 :: String -> r a -> r b
  con2 :: String -> r a -> r b -> r c
  con3 :: String -> r a -> r b -> r c -> r d
  conList :: String -> [r a] -> r b

class DEF r where
  def :: String -> r a

data Set0 a

class SET0 r where
  _ℕ :: r (Set0 ℕ)
  _String :: r (Set0 String)
  _List :: r (Set0 (a -> [a]))
  _Tree :: r (Set0 (a -> Tree a))
  _Interactive :: r (Set0 Interactive)
  _Program :: r (Set0 (a -> Program a))

  _App :: r (Set0 (a -> b)) -> r (Set0 a) -> r (Set0 b)

class DEFINITION r where
  simpleDefinition :: String -> r (Set0 a) -> r a -> r ()

class MAGIC r where
  magic :: r a -> r b

class LiftLIT a where
  symLift :: LIT r => a -> r a
  symLiftList :: LIT r => [a] -> r [a]
  symLiftList = list . map symLift

instance LiftLIT Char where
  symLift = undefined
  symLiftList = text
instance LiftLIT Integer where symLift = num
instance LiftLIT a => LiftLIT [a] where
  symLift = symLiftList
instance LiftLIT a => LiftLIT (Tree a) where
  symLift (Node x xs) = nodeT (symLift x) (symLift xs)

newtype R a = R { unR :: a }

instance Functor R where
  fmap = liftA

instance Applicative R where
  pure = R
  R f <*> R x = R (f x)

instance LIT R where
  num  = R . fromIntegral
  text = R
  list = R . map unR
  nodeT = liftA2 node

instance OPS R where
  (*:) = liftA2 (*)
  (+:) = liftA2 (+)
  (∸) = liftA2 (-)
  (÷) = liftA2 div
  (++:) = liftA2 (++)
  showT = fmap show
  printT x = R $ Interactive [unR x]
  x >>: y = R . Interactive $ ri x ++ ri y where ri = runInteractive . unR
  -- printT = fmap putStr
  -- (>>:) = liftA2 (>>)

newtype T a = T { unT :: Tree String }

-- liftT :: (a -> b) -> T a -> T b
-- liftT2 :: (a -> b -> c) -> T a -> T b -> T c
-- liftT3 :: (a -> b -> c -> d) -> T a -> T b -> T c -> T d

instance LIT T where
  num = con1 "num" . T . int
  text = con1 "text" . T . str
  list = conList "list"
  nodeT = con2 "node"

instance CON T where
  con0 x = T $ node x []
  con1 op = T . node op . return . unT
  con2 op (T t) (T u) = T $ node op [t, u]
  con3 op (T t) (T u) (T v) = T $ node op [t, u, v]
  conList op = T . node op . map unT

instance OPS T where
  (*:) = con2 "*"
  (+:) = con2 "+"
  (∸) = con2 "∸"
  (÷) = con2 "÷"
  (++:) = con2 "++"
  showT = con1 "show"
  printT = con1 "print"
  (>>:) = con2 ">>"

instance LET T where
  letH x t f = con3 "let" (T . str $ x) t (f (con1 "var" . T . str $ x))

lamT :: String -> String -> (T a -> T b) -> T (a -> b)
lamT var x f = con2 "λ" (T . str $ x) (f (con1 var . T . str $ x))

instance LAM T where
  lam = lamT "var"

instance APP T where
  app = con2 "app"

instance MAGIC T where
  magic (T x) = T x

instance DEF T where
  def = con0

newtype Program a = Program { unProgram :: a }
newtype Prog r a = Prog { unProg :: r (Program a) }

{-
num' :: LIT r => ℕ -> r (Program r1 ℕ)
num' = undefined

text' :: LIT r => String -> r (Program r1 String)
text' = undefined
-}

class CON r => PROGRAM r where
  program :: r a -> r (Program a)

  -- these are not used

  numPr  :: ℕ -> r (Program ℕ)
  textPr :: String -> r (Program String)
  -- listPr :: r [Program a] -> r (Program [a])
  -- treePr :: r (Tree (Program a)) -> r (Program 
  nodePr :: r (Program a) -> r (Program [Tree a]) -> r (Program (Tree a))
  (*::)  :: r (Program ℕ) -> r (Program ℕ) -> r (Program ℕ)

  numPr = unProg . num
  textPr = unProg . text
  --listPr = conList "`list"
  nodePr = con2 "`node"
  (*::) = con2 "`*"

instance PROGRAM P where
  program (P x) = P x

instance PROGRAM r => LIT (Prog r) where
  num = Prog . program . con1 "`num" . num
  text = Prog . program . con1 "`text" . text
  list = conList "`list"
  nodeT = con2 "`node"

instance PROGRAM r => CON (Prog r) where
  con0 = Prog . con0
  con1 op = Prog . con1 op . unProg
  con2 op (Prog t) (Prog u) = Prog $ con2 op t u
  con3 op (Prog t) (Prog u) (Prog v) = Prog $ con3 op t u v
  conList op = Prog . conList op . map unProg

instance PROGRAM r => OPS (Prog r) where
  (*:)   = con2 "`*"
  (+:)   = con2 "`+"
  (∸)    = con2 "`∸"
  (÷)    = con2 "`÷"
  (++:)  = con2 "`++"
  showT  = con1 "`show"
  printT = con1 "`print"
  (>>:)  = con2 "`>>"

{-
instance LAM Prog where
instance APP Prog where
instance DEF Prog where
-}

newtype Nom r a = Nom { unNom :: r a }

instance CON r => LAM (Nom r) where
  lam x f = Nom $ con2 "ƛ" (text x) (unNom $ f (Nom $ varN x))

instance CON r => LET (Nom r) where
  letH x (Nom t) f = Nom $ con3 "Let" (text x) t (unNom $ f (Nom $ varN x))

instance CON r => APP (Nom r) where
  app (Nom t) (Nom u) = Nom $ con2 "_·_" t u

instance MAGIC r => MAGIC (Nom r) where
  magic (Nom t) = Nom $ magic t

varN :: CON r => String -> r a
varN = con1 "V" . text

{-
data Tm a
newtype TmR r a = TmR { unTmR :: r (Tm a) }

instance CON r => APP (TmR r) where
-}

class DB r where
  lamD :: r b -> r (a -> b)
  letD :: r a -> r b -> r b
  varD :: Int -> r a

instance DB T where
  {-
  lamD = con1 "ƛ"
  letD = con2 "Let"
  varD = con1 "V" . T . int
  -}
  lamD = con1 "λ"
  letD = con2 "let"
  varD = con1 "var" . T . int

prettyAgdaList :: [Doc] -> Doc
prettyAgdaList [] = txt "[]"
prettyAgdaList xs = encloseSepSpacy P.lbracket P.rbracket P.comma xs

type Prec = Int

newtype P a = P { unP :: Prec -> Doc }

appPrec, topPrec, letPrec, lamPrec :: Prec
appPrec = 10
topPrec = 0
lamPrec = 1
letPrec = 2

parenIf :: (Int -> Bool) -> Doc -> (Int -> Doc)
parenIf p doc prec = if p prec then P.parens doc else doc


varP :: String -> P a
varP = P . const . txt

prefixP :: String -> P a -> P b
prefixP = app . varP

prefixP2 :: String -> P a -> P b -> P c
prefixP2 op t u = prefixP op t `app` u

infixrP, infixlP :: String -> Prec -> P a -> P b -> P c
infixGenP :: (Int -> Int) -> (Int -> Int) -> String -> Prec -> P a -> P b -> P c

infixGenP f g op prec (P t) (P u) = P . parenIf (>= prec) . P.group . P.align $ t (f prec) <+> txt op <$> u (g prec)
infixlP = infixGenP pred id
infixrP = infixGenP id pred

instance LIT P where
  num = P . const . pretty
  text = P . const . pretty . prettyShowString
  list xs = P . const $ prettyAgdaList (map (($topPrec) . unP) xs)
  nodeT = prefixP2 "node"

infixr 5 ++:
infixl 1 >>:
infixl 6 +: -- ∸
infixl 7 *: -- ÷

instance OPS P where
  showT = prefixP "show"
  printT = prefixP "print"
  (*:) = infixlP "*" 7
  (+:) = infixlP "+" 6
  (∸) = infixlP "∸" 6
  (÷) = infixlP "÷" 7
  (++:) = infixrP "++" 5
  (>>:) = infixlP ">>" 1

instance DEF P where
  def = con0

appDoc :: (Prec -> Doc) -> (Prec -> Doc) -> (Prec -> Doc)
appDoc t u = parenIf (>= appPrec) . P.group . P.hang 2 $ t (pred appPrec) <$> u appPrec

instance LAM P where
  lam x f = P . parenIf (>= lamPrec) . P.group . P.hang 2
              $ txt "λ" <+> txt x <+> txt "→" <$> unP (f (P(const (txt x)))) lamPrec

instance APP P where
  app (P t) (P u) = P $ appDoc t u

instance LET P where
  letH x (P t) f = P . parenIf (>= letPrec) . P.group . P.align
                     $ txt "let" <+> txt x <+> P.group (P.hang 2 (txt "=" <$> t topPrec))
                   <+> txt "in" <$> unP (f (P(const (txt x)))) topPrec{-letPrec-}

instance CON P where
  con0 = P . const . pretty
  con1 = app . con0
  con2 op t u = app2 (con0 op) t u
  con3 op t u v = app3 (con0 op) t u v
  conList op = P . foldl appDoc (const (pretty op)) . map unP

instance DEFINITION P where
  simpleDefinition x (P ty) (P body) = P . const $
    txt x <+> txt ":" <+> ty topPrec <$>
    txt x <+> txt "=" <+> body topPrec

instance SET0 P where
  _ℕ           = con0 "ℕ"
  _String      = con0 "String"
  _List        = con0 "List"
  _Tree        = con0 "Tree"
  _Interactive = con0 "Interactive"
  _Program     = con0 "Program"
  _App (P t) (P _u) = P t -- $ appDoc t u -- TODO Hack to print Program A as Program

instance MAGIC P where
  magic (P x) = P x

prettyP :: P a -> Doc
prettyP (P x) = x topPrec

newtype NoLet r a = NoLet { noLet :: r a }
  deriving (LIT, OPS)

instance LET r => LET (NoLet r) where
  letH _ t f = f t

instance LET R where
  letH _ t f = f t

newtype EA r a = EA { explicitApplications :: r a }
  deriving (LIT, DEF, APP)

app2 :: APP r => r (a -> b -> c) -> r a -> r b -> r c
app2 f x y = f `app` x `app` y

app3 :: APP r => r (a -> b -> c -> d) -> r a -> r b -> r c -> r d
app3 f x y z = f `app` x `app` y `app` z

instance (LIT r, APP r, DEF r) => OPS (EA r) where
  (*:)   = app2 (def "_*_")
  (+:)   = app2 (def "_+_")
  (∸)    = app2 (def "_∸_")
  (÷)    = app2 (def "_÷_")
  (++:)  = app2 (def "_++_")
  (>>:)  = app2 (def "_>>_")
  showT  = app  (def "show")
  printT = app  (def "print")

-- Just for the fun, a baby version of NBE
nbe :: LiftLIT a => (forall r. (OPS r, LET r) => r a) -> forall r. LIT r => r a
nbe (R x) = symLift x

{-# LANGUAGE QuasiQuotes, OverloadedStrings, UnicodeSyntax #-}
{-# OPTIONS_GHC -F -pgmF frquotes -fno-warn-missing-signatures #-}
-- VIM :source config.vim

import Kit

import Paper.Keys
import Paper.Snippets
import Paper.Intro
import Paper.Overview
import Paper.Context
import Paper.TermStructure
import Paper.Cata
import Paper.Scopes
import Paper.TermCmp
import Paper.Norm
import Paper.NbE
import Paper.CC
import Paper.CPS
import Paper.Related
import Paper.Discussion
import System.IO (hPutStrLn, stderr)

--import qualified MiniTikz.Builder as D -- hiding (node)
--import MiniTikz.Builder (right, below, nodeDistance, oF, dnode, spath, scope)

--import System.Directory (copyFile)

title =  «Names For Free --- Polymorphic Views of Names and Binders»
  -- «Parametric Nested Abstract Syntax» -- Sounds like it's for a representation
  --
  -- «A Classy Kind of Nested Abstract Syntax»
  -- «Implementing Names and Binders with Polymorphism»
-- Ingredients:
-- Classes
-- Polymorphism
-- Nested


authors = [ («Jean-Philippe Bernardy» , «bernardy@chalmers.se» , «Chalmers University of Technology and University of Gothenburg»)
           ,(«Nicolas Pouillard»      , «npou@itu.dk»          , «IT University Copenhagen»)
          ]
abstract = [texFile|abstract|]
keywords = [texFile|keywords|]
_Agda's = «{_Agda}'s»

{-
Arguments for having v ▹ a instead of a ▹ v

  * If we consider v to be a dummy type then
    this functor ((▹) v) seems more common than
    this functor ((▹) a)
  * Same direction as List.(:), Nompa.(◅), Bound.Var, (∈)
  * If we see this as a morphism (inj :: v -> a) then
    the order is the same

Arguments for keeping the current order

  * Same direction as Γ,x

fmap     :: Functor f     => (a -> b) -> f a -> f b
(=<<)    :: Monad   m     => (a -> m b) -> m a -> m b
traverse :: Applicative f => (a -> f b) -> t a -> f (t b)

isClosed :: Foldable f => f a -> Bool
closed   :: Traversable f => f a -> Maybe (f b)
elem     :: (Foldable t, Eq a) => a -> t a -> Bool
vacuous  :: Functor f => f Void -> f a

On top of Bound:

  type a ▹ v = Var v a

  class v ∈ a where
    inj :: v → a

  instance x ∈ (γ ▹ x) where
    inj = B

  instance (x ∈ γ) ⇒ x ∈ (γ ▹ y) where
    inj = F . inj

  var :: ∀ f v a. (v ∈ a, Monad f) ⇒ v → f a
  var = return . inj

  abs :: ∀ f a. (∀ v. v → f (a ▹ v)) → f (Succ a)
  abs k = k ()

  unpack :: f (Succ a) → (∀ v. v → f (a ▹ v) → r) → r
  unpack e k = k () e

  pack :: Functor tm ⇒ v → tm (a ▹ v) → tm (Succ a)
  pack x = fmap (bimap id (const ()))

  lam :: ∀ a. (∀ v. v → Tm (a ▹ v)) → Tm a
  lam k = Lam (abs k)

  -- Scopes

  abs :: ∀ f a. Monad f ⇒ (∀ v. v → f (a ▹ v)) → Scope () f a
  abs k = toScope . k ()

  lam :: ∀ a. (∀ v. v → Tm (a ▹ v)) → Tm a
  lam k = Lam (abs k)

  class a ⊆ b where
    injMany :: a → b

  instance a ⊆ a where injMany = id

  instance Zero ⊆ a where injMany = magic

  instance (γ ⊆ δ) ⇒ (γ ▹ v) ⊆ (δ ▹ v) where
    injMany = bimap injMany id

  instance (a ⊆ c) ⇒ a ⊆ (c ▹ b) where
    injMany = F . injMany

  wk :: (Functor f, γ ⊆ δ) ⇒ f γ → f δ
  wk = fmap injMany

* Term structure:
    * Monad =>
        * substitution
        * Functor (=> renaming)
        * pure scope manipulation
            * a close term can inhabit any "world": 'vacuous'
    * Traversable =>
        * effectful scope manipulation
            * 'traverse (const Nothing)' is 'closed'
        * Foldable =>
            * fold over the free variables
            * monoidal action on the free-vars
                * 'all (const False)' is 'isClosed'
                * toList
                * elem
* Scope as an abstraction:
    * Once we have an abstraction the concrete definition
      can be changed according to different criterions:
        * efficiency (as the 'Scope' from Bound)
        * simplicity (improve reasoning)

* Nice packing and unpacking of scopes
    * could be better than 'abstract'/'instantiate'
    * higher-order style:
        * ∀ v. v → f (a ▹ v)
        * nice constructions: lam λ x → lam λ y → ...
        * nice unpacking: unpack λ x t → ...
    * nominal style:
        * ∃ v. (v , f (a ▹ v))
        * "fresh x in ..." stands for "case fresh of Fresh x -> ..."
        * fresh x in fresh y in lam x (lam y ...)

-}


  {- NP:
  These throwaway arguments might be a bit worrisome. A more involved
  version would use a type known as Tagged

  data Tagged a b = Tagged b

  Or more specific to our usage

  data Binder v = TheBinder
  -- Iso to Tagged v ()

  unpack :: (∀ v. v → tm (w ▹ v)) →
            (∀ v. Binder v → tm (w ▹ v) → a) → a
  unpack b k = k TheBinder (b TheBinder)

  remove :: Binder v → [a ▹ v] → [a]
  remove _ xs = [x | Old x ← xs]

  ...
  in this case we should also have:
  (∀ v. Binder v → tm (w ▹ v))
  -}


body onlyInCode = execWriter $ do -- {{{

  onlyInCode $ do 
     [haskellP|
     |{-# LANGUAGE RankNTypes, UnicodeSyntax,
     |    TypeOperators, GADTs, MultiParamTypeClasses,
     |    FlexibleInstances, UndecidableInstances,
     |    IncoherentInstances, ScopedTypeVariables, StandaloneDeriving #-}
     |module PaperCode where
     |import Prelude hiding (elem,any,foldl,foldr)
     |import Control.Monad
     |import Control.Applicative
     |import Data.Foldable
     |import Data.Traversable
     |import Data.List (nub,elemIndex)
     |import Data.Maybe
     |-- import Data.Bifunctor 
     |
     |main :: IO ()
     |main = putStrLn "It works!"
     |]

  notetodo «Hybrid! mapOld mapNew»
  notetodo «more related work with McBride»
  notetodo «Ack Demtech fundings»
  {-
  notetodo «unify the terminology names/context/free variables (when the rest is ready)»
     NP: All these three notions names/context/free variables have to
         be used appropriately. I would not "unify" them.
         * A name is either bound or free
         * A context is where a name makes sense
         * A free variable makes reference to somewhere in a term (the Var constructor)
   -}
  introDoc
  overviewDoc onlyInCode
  contextDoc onlyInCode
  termStructureDoc
  scopesDoc onlyInCode


  section $ «Bigger Examples» `labeled` examples

  when False termCmpDoc

  normDoc
  when False docNbE
  ccDoc onlyInCode
  cpsDoc
  relatedDoc onlyInCode
  discussionDoc onlyInCode

appendix onlyInCode = execWriter . onlyInCode{-this hiddes the whole appendix-} $ do
  section $ «Implementation details» `labeled` implementationExtras
  subsection «Traversable»
  [haskellP|
  |instance Foldable Tm where
  |  foldMap = foldMapDefault
  |]

  subsection «Extend» -- TODO
  [haskellP|
  |extend :: (v, r) → (a → r) → (a ▹ v → r)
  |extend (_, x) _ (New _) = x
  |extend _      f (Old x) = f x
  |]

  subsection «Normalization»
  normAppendix

  subsection «CPS»
  cpsAppendix

  subsection «Closure Conversion»
  ccAppendix

  {- commented out until there is a reference to it from the body
  section $ «NomPa details»
  [haskellP|
  |-- ¬Nameø : ¬ (Name ø)
  |noEmptyName :: Zero → a
  |noEmptyName = magic
  |
  |-- nameᴮ : ∀ {α} b → Name (b ◅ α)
  |name :: b → a ▹ b
  |name = New
  |
  |-- ⊆-# : ∀ {α b} → b # α → α ⊆ (b ◅ α)
  |import_ :: a → a ▹ b
  |import_ = Old
  |
  |-- In Agda: exportᴺ? : 
  |-- ∀ {b α} → Name (b ◅ α) → Maybe (Name α)
  |exportM :: a ▹ b → Maybe a
  |exportM (New _) = Nothing
  |exportM (Old x) = Just x
  |
  |-- In Agda: exportᴺ : 
  |-- ∀ {α b} → Name (b ◅ α) → Name (b ◅ ø) ⊎ Name α
  |export :: a ▹ b → Either (Zero ▹ b) a
  |export (New x) = Left (New x)
  |export (Old x) = Right x
  |
  |-- ⊆-◅ : ∀ {α β} b → α ⊆ β → (b ◅ α) ⊆ (b ◅ β)
  |-- fmap of (▹ b)
  |-- ⊆-ø : ∀ {α} → ø ⊆ α
  |-- magic :: Zero → a
  |]
  -}
  stopComment
  stopComment
  stopComment
  stopComment
  stopComment
  return ()
-- }}}

-- {{{ build
-- NP: what about moving this outside, such as run.sh
-- JP: Nope. I'd rather not leave emacs haskell mode.
refresh_jp_bib = do
  let jpbib = "../../gitroot/bibtex/jp.bib"
  e ← doesFileExist jpbib
  when e $ do hPutStrLn stderr "refreshing bib"
              void . system $ "cp " ++ jpbib ++ " ."

main = do
  args ← getArgs
  refresh_jp_bib
  let latexDoc = doc (const (return ()))
      comments = doc id
  case args of
    ["--tex"]      → printLatexDocument latexDoc
    ["--comments"] → printComments      comments
    [] → do
      writeCommentsTo "PaperCode.hs"  comments
      compile ["sigplanconf"] "main"  latexDoc
    _ → error "unexpected arguments"

categ = Kit.cat «D.3.3» «Language Constructs and Features» «»


doc onlyInCode = document title authors keywords abstract categ (body onlyInCode) (appendix onlyInCode)
-- }}}

-- vim: foldmarker
-- -}


{-

∇ in F2:

Typing:

  Γ,β ⊢ t : ∇α. T[α] 
---------------------    ∇-elim
   Γ ⊢ t @ β : T[β]

note: to make sure that a single variable is not used twice /by the
∇-elim rule/ it's eaten up.  (Technically β should be marked 'eaten'
in the context instead of being summarily removed, since it can be
used as an index in some type family (a subterm of T))


   Γ,α ⊢ t : T[α]
----------------------   ∇-intro
  Γ ⊢ ∇α.t : ∇α. T[α]


Computation:

(∇α.t) @ β  ---> t[β/α]
∇α.(t @ β)  ---> ∇β.t

-- not sure about the rule above, what about this:
∇α.(t @ α)  ---> t

fresh :: ∇v.v
fresh = ∇v.v

var :: ∇v. Tm v
var = ∇v. Var v

Lam :: (∇v. Tm (a ▹ v)) → Tm a

apTm = Lam (α, Lam (β, App (Old (New (var @ α))) (New (var @ β))))

case t of
  Lam (b :: ∇v.Tm(a▹v)) ->
    Lam (∇α. App (b @ α) (b @ α)) -- ill typed because α is used twice
    -- but
    Lam (∇α. let t = b @ α in App t t) -- is fine

Pie in the sky:
---------------

We can then represent binders as:

∇v. v ⊗ (v → Tm (a ▹ v))


- 'destroying'/analysis of the term is done by applying the function to the 1st
  argument of the pair.
- constructing a term feels like it should use excluded middle (of LL) to
  produce the argument of the pair from whatever is passed to the function.
  Intuitively, you can do this because any code using either component of the pair
  must use the other part as well. Unfortunately I cannot see how to implement this
  technically.


Linear logic treatment of ∇:

   α; Γ, A[α] ⊢
------------------ ∇
   Γ, ∇α.A[α] ⊢


∇ eliminates with itself:


   α; Γ, A[α] ⊢              β; Δ, ~A[β] ⊢
------------------ ∇      ------------------ ∇
   Γ, ∇α.A[α] ⊢              Γ, ∇β.~A[β] ⊢
----------------------------------------------- cut
        Γ, Δ ⊢


   α; Γ, A[α] ⊢              α; Δ, ~A[α] ⊢
----------------------------------------------- cut
      α; Γ, Δ ⊢ prf
   --------------------
      Γ, Δ ⊢ να. prf


For the fun we can also see the following, but that's just
a bonus:

∇ eliminates with ∃ (identical to the above)
∇ eliminates with ∀:


  α; Γ, A[α] ⊢              Δ, ~A[B] ⊢
------------------ ∇      ------------------ ∀
   Γ, ∇α.A[α] ⊢              Γ, ∀β.~A[β] ⊢
----------------------------------------------- cut
        Γ, Δ ⊢


   Γ, A[~B] ⊢              Δ, ~A[B] ⊢
----------------------------------------------- cut
        Γ, Δ ⊢


So it's easy to see that ∇ is a subtype of ∃ and ∀.



-}


--  LocalWords:  pollacksatoricciotti belugamu fincites nestedcites
--  LocalWords:  mcbridemckinna birdpaterson altenkirchreus nbecites
--  LocalWords:  bergernormalization licataharper pouillardunified tm
--  LocalWords:  parametricityIntegrationCites kellerparametricity FV
--  LocalWords:  bernardycomputational bernardytypetheory Agda's apTm
--  LocalWords:  hereditarycites polymorphism intodo notetodo haskellFP
--  LocalWords:  notecomm doComment ParItemW startComment stopComment
--  LocalWords:  commentWhen commentCode unpackCode canEta freshFor
--  LocalWords:  isOccurenceOf canEtaWithSig haskellP Nompa morphism TmB
--  LocalWords:  fmap isClosed Foldable Traversable untyped VarB AppB
--  LocalWords:  representable debruijnlambda LamB apB naïve bimap vx
--  LocalWords:  parameterizes onlyInCode cardinality untag Bifunctor
--  LocalWords:  apNested const unicity nabla natively NExistScope
--  LocalWords:  quantifing packGen lamP freeVars recurse occursIn vf
--  LocalWords:  injMany functoriality functorial parameterized atVar
--  LocalWords:  monadic injective Monads Kleisli liftSubst SuccScope
--  LocalWords:  UnivScope substituteOut effectful mcbrideapplicative
--  LocalWords:  bitraverse traversable toList forall ExistScope cata
--  LocalWords:  existentials isomorphisms succToUniv univToSucc pVar
--  LocalWords:  equational Transcoding Paterson fegarasrevisiting
--  LocalWords:  bernardyproofs equationally succToExist existToSucc
--  LocalWords:  FunScope fmapFunScope returnFunScope TmAlg
--  LocalWords:  bindSuccScope bindFunScope funToUniv existToFun pLam
--  LocalWords:  funToSucc succToFun sizeEx pApp extendAlg pVarSucc
--  LocalWords:  cataSize sizeAlg toNat cmpTm Cmp cmp extendCmp LamNo
--  LocalWords:  Neutr redexes foldl docNbE dmath env
--  LocalWords:  guillemettetypepreserving llbracket rrbracket ldots
--  LocalWords:  mathnormal langle rangle venv LetOpen VarLC AppLC yn
--  LocalWords:  infixl letOpen idxFrom fromJust elemIndex TmC HaltC
--  LocalWords:  chlipalaparametric AppC LetC LamC PairC FstC SndC eq
--  LocalWords:  VarC haltC appC letC lamC pairC fstC sndC varC fst
--  LocalWords:  snd lamPairC inlining washburnboxes caml OCaml suc
--  LocalWords:  Brujn DelayedScope TmD VarD LamD AppD TmH LamH AppH
--  LocalWords:  atkeyhoas TmF apTmF Kripke tmToTmF PHOAS TmP VarP vn
--  LocalWords:  AppP joinP modularity mcbridenot NomPa Nameø refl
--  LocalWords:  Idris equalities boundkmett NScope NUnivScope
--  LocalWords:  millerproof Axelsson Gustafsson

{-

                       “Binder representations in Agda”

                              Nicolas Pouillard,
                       IT University of Copenhagen (ITU)

             _     _____ __  __ _____ ____  _ ____   ___  _ ____
            | |   |  ___|  \/  |_   _|  _ \( )___ \ / _ \/ |___ \
            | |   | |_  | |\/| | | | | |_) |/  __) | | | | | __) |
            | |___|  _| | |  | | | | |  __/   / __/| |_| | |/ __/
            |_____|_|   |_|  |_| |_| |_|     |_____|\___/|_|_____|

                         September 9 2012, Copenhagen

-}
module binding-representations where

{-
 ___       _                 _            _   _
|_ _|_ __ | |_ _ __ ___   __| |_   _  ___| |_(_) ___  _ __
 | || '_ \| __| '__/ _ \ / _` | | | |/ __| __| |/ _ \| '_ \
 | || | | | |_| | | (_) | (_| | |_| | (__| |_| | (_) | | | |
|___|_| |_|\__|_|  \___/ \__,_|\__,_|\___|\__|_|\___/|_| |_|

-}
-- {{{
module intro where

    data Bool : Set where
      true  : Bool
      false : Bool

    data ℕ : Set where
      zero : ℕ
      suc  : (n : ℕ) → ℕ

    _+_ : ℕ → ℕ → ℕ
    zero  + n = n
    suc m + n = suc (m + n)

    data Maybe (A : Set) : Set where
      just    : (x : A) → Maybe A
      nothing : Maybe A

    data Fin : ℕ → Set where
      zero : {n : ℕ} → Fin (suc n)
      suc  : {n : ℕ} (i : Fin n) → Fin (suc n)
-- }}}

-- {{{
open import Data.Char using (Char) renaming (_==_ to _==ᶜ_)
open import Data.Maybe.NP -- https://github.com/crypto-agda/agda-nplib
  renaming (⟪_·_⟫? to ⟪_∙_⟫?;
            ⟪_·_·_⟫? to ⟪_∙_∙_⟫?;
            ⟪_·_·_·_⟫? to ⟪_∙_∙_∙_⟫?)
open import Data.List using (List; length; foldl; []; _∷_; _++_) renaming (map to map[])
open import Data.Nat.NP
open import Data.Nat.Logical
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Bool.NP
open import Data.Product
open import Data.Unit
import Data.Fin as Fin
open Fin using (Fin; zero; suc; #_)
open import Data.Empty
open import Data.String as String renaming (_==_ to _==ˢ_; _++_ to _++ˢ_)
open import Function.NP
open import Relation.Binary
open import Relation.Binary.Logical
import Relation.Binary.PropositionalEquality.NP as ≡
open ≡ using (_≡_; _≗_)
open import Text.Parser
  hiding (join; _>>=_)
  renaming (⟪_·_⟫ to ⟪_∙_⟫;
            ⟪_·_·_⟫ to ⟪_∙_∙_⟫;
            ⟪_·_·_·_⟫ to ⟪_∙_∙_∙_⟫)
open import Text.Printer
import Level as L
open M? L.zero using ()
  renaming (_>>=_ to _>>=?_;
            _=<<_ to _=<<?_)
-- }}}

-- {{{
module missing-lib where
    predWith : ∀ {A : Set} → A → (ℕ → A) → ℕ → A
    predWith z _ zero    = z
    predWith _ s (suc n) = s n

    fromℕ? : ∀ n → ℕ →? Fin n
    fromℕ? zero    x       = nothing
    fromℕ? (suc n) zero    = just zero
    fromℕ? (suc n) (suc x) = map? suc (fromℕ? n x)

    Fin-elim : ∀ {A : Set} {n} → A → (Fin n → A) → Fin (suc n) → A
    Fin-elim z _ zero    = z
    Fin-elim _ s (suc n) = s n

    liftFin : ∀ {m n} → (Fin m → Fin n) → Fin (suc m) → Fin (suc n)
    liftFin f = Fin-elim zero (suc ∘ f)

    fromFin : ∀ {n} → Fin n → ∀ {a} {A : Set a} → Maybe^ n A
    fromFin zero    = nothing
    fromFin (suc x) = just (fromFin x)

    toFin : ∀ {n} → Maybe^ n ⊥ → Fin n
    toFin {suc n} nothing  = zero
    toFin {suc n} (just x) = suc (toFin x)
    toFin {zero}  ()

    isSpace : Char → Bool
    isSpace = (_==ᶜ_ ' ')

    spaces : Parser ⊤
    spaces = manySat isSpace *> pure _

    someSpaces : Parser ⊤
    someSpaces = someSat isSpace *> pure _

    tok : Char → Parser ⊤
    tok c = spaces *> char c *> pure _

    bracket : ∀ {A} → Char → Parser A → Char → Parser A
    bracket start p stop = tok start *> p <* tok stop

    ⟦Bool⟧⇒≡ : ⟦Bool⟧ ⇒ _≡_
    ⟦Bool⟧⇒≡ ⟦true⟧  = ≡.refl
    ⟦Bool⟧⇒≡ ⟦false⟧ = ≡.refl

open missing-lib
-- }}}

{-
 ____  _        _
/ ___|| |_ _ __(_)_ __   __ _ ___
\___ \| __| '__| | '_ \ / _` / __|
 ___) | |_| |  | | | | | (_| \__ \
|____/ \__|_|  |_|_| |_|\__, |___/
                        |___/
-}
-- {{{
idˢ = "λx. x"
apˢ = "λf.λx. f x"
∘ˢ = "λf.λg.λx.f (g x)"
Kˢ = "λx.λy.x"
Sˢ = "λf.λg.λx.f x (g x)"
flipˢ = "λf.λx.λy.f y x"
δˢ = "λx.x x"
Ωˢ = "(λx. x x) (λx. x x)"

examplesˢ : List String
examplesˢ = idˢ ∷ apˢ ∷ ∘ˢ ∷ Kˢ ∷ Sˢ ∷ flipˢ ∷ δˢ ∷ Ωˢ ∷ []
-- }}}

{-
    _   _
   / \ | |_ ___  _ __ ___  ___
  / _ \| __/ _ \| '_ ` _ \/ __|
 / ___ \ || (_) | | | | | \__ \
/_/   \_\__\___/|_| |_| |_|___/

-}
-- {{{
infixl 4 _·_
data Tmᴬ (A : Set) : Set where
  -- {{{
  V   : (x : A) → Tmᴬ A
  ƛ   : (b : A) (t : Tmᴬ A) → Tmᴬ A
  _·_ : (t u : Tmᴬ A) → Tmᴬ A
  -- }}}

mapᴬ : ∀ {A B} → (A → B) → Tmᴬ A → Tmᴬ B
-- {{{
mapᴬ f (V x)   = V (f x)
mapᴬ f (ƛ b t) = ƛ (f b) (mapᴬ f t)
mapᴬ f (t · u) = mapᴬ f t · mapᴬ f u
-- }}}

{- Map laws (derivable from parametricity)

mapᴬ-lem :
    (f : ∀ {A} → Tmᴬ A → Tmᴬ A)
    → ∀ {A B} (g : A → B) → mapᴬ g ∘ f ≗ f ∘ mapᴬ g

mapᴬ-lem' :
    (f : ∀ {A} → Tmᴬ A → Bool)
    → ∀ {A B} (g : A → B) → f ≗ f ∘ mapᴬ g
-}

Tmˢ = Tmᴬ String

module Named where

  module Undesirable where
    unƛ : ∀ {A} → Tmᴬ A → Tmᴬ A
    unƛ (V x)   = V x
    unƛ (ƛ b t) = unƛ t
    unƛ (t · u) = unƛ t · unƛ u

    bv : ∀ {A} → Tmᴬ A → List A
    bv (V x)   = []
    bv (ƛ b t) = b ∷ bv t
    bv (t · u) = bv t ++ bv u

    unα : ∀ {A} → Cmp A → Cmp (Tmᴬ A)
    unα cmp (ƛ b₀ _) (ƛ b₁ _) = cmp b₀ b₁
    unα _   _        _        = false

module TmˢParser where
    kwdChars : List Char
    kwdChars = String.toList "λ(.) "

    var : Parser String
    var = ⟪ String.fromList ∙ spaces *> someNoneOf kwdChars ⟫

    someSpacesOrLookKwdChar : Parser ⊤
    someSpacesOrLookKwdChar = lookHeadSomeOf kwdChars ⟨|⟩ someSpaces

    tm  : ℕ → Parser Tmˢ
    tm′ : ℕ → Parser Tmˢ

    -- {{{
    tm n = ⟪ foldl _·_ ∙ tm′ n ∙ many n (someSpacesOrLookKwdChar *> tm′ n) ⟫

    tm′ (suc n) =  bracket '(' (tm n) ')'
               ⟨|⟩ ⟪ ƛ ∙ bracket 'λ' var '.' ∙ tm n ⟫
               ⟨|⟩ ⟪ V ∙ var ⟫
    tm′ zero    =  empty
    -- }}}

parseTmˢ? : String →? Tmˢ
parseTmˢ? s = runParser (TmˢParser.tm n <* eof) ℓ
  where ℓ = String.toList s
        n = length ℓ

parseList : ∀ {A : Set} → (String →? A) → List String →? List A
parseList p []       = just []
parseList p (x ∷ xs) = ⟪ _∷_ ∙ p x ∙ parseList p xs ⟫?

parseTmˢ : T[ parseTmˢ? ]
parseTmˢ = F[ parseTmˢ? ]

Ω™ˢ : Tmˢ
Ω™ˢ = parseTmˢ Ωˢ

examples™ˢ : List Tmˢ
examples™ˢ = from-just (parseList parseTmˢ? examplesˢ)

module TmˢPrinter where
    open PrEnv

    top = mk 2
    app = mk 1
    atm = mk 0

    prTm : PrEnv → Pr Tmˢ
    prTm ℓ (ƛ b t) = paren top ℓ (` "λ" ∘ ` b ∘ ` ". " ∘ prTm top t)
    prTm ℓ (t · u) = paren app ℓ (prTm app t ∘ ` " " ∘ prTm atm u)
    prTm ℓ (V x)   = ` x

showTmˢ : Tmˢ → String
showTmˢ t = prTm top t "" where open TmˢPrinter
-- }}}

{-
     _        ____             _  _
  __| | ___  | __ ) _ __ _   _(_)(_)_ __
 / _` |/ _ \ |  _ \| '__| | | | || | '_ \
| (_| |  __/ | |_) | |  | |_| | || | | | |
 \__,_|\___| |____/|_|   \__,_|_|/ |_| |_|
                               |__/

Reference:
  Nicolaas G. de Bruijn
  1972
  Lambda-Calculus Notation with Nameless Dummies: a Tool
  for Automatic Formula Manipulation with Application to
  the Church-Rosser Theorem
-}
-- {{{
Vᴮ : Set
Vᴮ = ℕ

data Tmᴮ : Set where
  -- {{{
  V   : (x : Vᴮ) → Tmᴮ
  ƛ   : (t : Tmᴮ) → Tmᴮ
  _·_ : (t u : Tmᴮ) → Tmᴮ
  -- }}}

→™ᴮ : Set
→™ᴮ = Tmᴮ → Tmᴮ

liftVᴮ : (Vᴮ → Vᴮ) → (Vᴮ → Vᴮ)
liftVᴮ f zero    = zero
liftVᴮ f (suc x) = suc (f x)

mapᴮ : (Vᴮ → Vᴮ) → Tmᴮ → Tmᴮ
-- {{{
mapᴮ f (V x)   = V (f x)
mapᴮ f (ƛ t)   = ƛ (mapᴮ (liftVᴮ f) t)
mapᴮ f (t · u) = mapᴮ f t · mapᴮ f u
-- }}}

module SubstTmᴮ where
    -- Type of term transformations
    -- {{{
    →™ : Set
    →™ = Tmᴮ → Tmᴮ
    -- }}}

    -- Type of substitutions
    -- {{{
    ⇶ : Set
    ⇶ = Vᴮ → Tmᴮ
    -- }}}

    -- Extend a substitution to one more binder
    -- {{{
    ⇑ : ⇶ → ⇶
    ⇑ f zero    = V zero
    ⇑ f (suc x) = mapᴮ suc (f x)
    -- }}}

    -- {{{
    [_] : ⇶ → →™
    [ θ ](V x)   = θ x
    [ θ ](ƛ t)   = ƛ ([ ⇑ θ ] t)
    [ θ ](t · u) = [ θ ] t · [ θ ] u
    -- }}}

    0≔ : Tmᴮ → ⇶
    0≔ t = predWith t V

    private
        test : [ 0≔ (ƛ (V 0 · V 1 · V 2)) ] (ƛ (V 0 · V 1))
             ≡ ƛ (V 0 · ƛ (V 0 · V 2 · V 3))
        test = ≡.refl

    β-red : →™
    β-red (ƛ t · u) = [ 0≔ u ] t
    β-red t         = t

module Tmˢ⇒ᴮ where
    Ren : Set
    Ren = String → ℕ

    _,,_ : String → Ren → Ren
    -- {{{
    (b ,, ρ) s = if b ==ˢ s then 0 else 1 + ρ s
    -- }}}

    [_] : Ren → Tmˢ → Tmᴮ
    -- {{{
    [ ρ ](V x)   = V (ρ x)
    [ ρ ](ƛ b t) = ƛ ([ b ,, ρ ] t)
    [ ρ ](t · u) = [ ρ ] t · [ ρ ] u
    -- }}}

    Tmˢ⇒ᴮ : Tmˢ → Tmᴮ
    -- {{{
    Tmˢ⇒ᴮ = [ const 0 ]
    -- }}}

open Tmˢ⇒ᴮ public using (Tmˢ⇒ᴮ)

parseTmᴮ? : String →? Tmᴮ
parseTmᴮ? s = map? Tmˢ⇒ᴮ (parseTmˢ? s)

parseTmᴮ : T[ parseTmᴮ? ]
parseTmᴮ = F[ parseTmᴮ? ]

examplesᴮ : List Tmᴮ
examplesᴮ = from-just (parseList parseTmᴮ? examplesˢ)

module Tmᴮ⇒ˢ where
    binder! : ℕ → String
    binder! 0 = "x"
    binder! 1 = "y"
    binder! 2 = "z"
    binder! (suc (suc (suc n))) = "x" ++ˢ showℕ n

    name! : (ℓ x : ℕ) → String
    -- {{{
    name! ℓ x = binder! (ℓ ∸ suc x)
    -- }}}

    [_] : ℕ → Tmᴮ → Tmˢ
    -- {{{
    [ ℓ ](V x)   = V (name! ℓ x)
    [ ℓ ](ƛ t)   = ƛ (binder! ℓ) ([ suc ℓ ] t)
    [ ℓ ](t · u) = [ ℓ ] t · [ ℓ ] u
    -- }}}

    Tmᴮ⇒ˢ : Tmᴮ → Tmˢ
    -- {{{
    Tmᴮ⇒ˢ = [ 0 ]
    -- }}}

open Tmᴮ⇒ˢ public using (Tmᴮ⇒ˢ)

showTmᴮ : Tmᴮ → String
showTmᴮ t = showTmˢ (Tmᴮ⇒ˢ t)

Ωᴮ : Tmᴮ
Ωᴮ = parseTmᴮ Ωˢ
-- }}}

{-
 _____ _
|  ___(_)_ __
| |_  | | '_ \
|  _| | | | | |
|_|   |_|_| |_|

References:
  * Thorsten Altenkirch [1993]
      "A Formalization of the Strong Normalization Proof for System F in LEGO"
  * Conor McBride and James McKinna [2004]
      "The view from the left"
-}

-- {{{
data Tmᶠ n : Set where
  -- {{{
  V    : (x : Fin n) → Tmᶠ n
  _·_  : (t u : Tmᶠ n) → Tmᶠ n
  ƛ    : (t : Tmᶠ (suc n)) → Tmᶠ n
  -- }}}

mapᶠ : ∀ {m n} → (Fin m → Fin n) → Tmᶠ m → Tmᶠ n
-- {{{
mapᶠ f (V x)   = V (f x)
mapᶠ f (t · u) = mapᶠ f t · mapᶠ f u
mapᶠ f (ƛ t)   = ƛ (mapᶠ (liftFin f) t)
-- }}}

module Traverseᶠ {m n} (f : ∀ ℓ → Fin (ℓ + m) → Tmᶠ (ℓ + n)) where
    tr : ∀ ℓ → Tmᶠ (ℓ + m) → Tmᶠ (ℓ + n)
    tr ℓ (V x)   = f ℓ x
    tr ℓ (ƛ t)   = ƛ (tr (suc ℓ) t)
    tr ℓ (t · u) = tr ℓ t · tr ℓ u

    traverse : Tmᶠ m → Tmᶠ n
    traverse = tr 0

open Traverseᶠ public using () renaming (traverse to traverseᶠ)

private
    module Undesirableᶠ where
        broken-add-V : ∀ {n} k ℓ → Fin (ℓ + n) → Tmᶠ (ℓ + (k + n))
        broken-add-V {n} k ℓ x
          rewrite +-assoc-comm ℓ k n
                = V (Fin.raise k x)

        broken-add : ∀ {n} k → Tmᶠ n → Tmᶠ (k + n)
        broken-add k = traverseᶠ (broken-add-V k)

        may-swap-app : ∀ n → Tmᶠ n → Tmᶠ n
        may-swap-app 0 (t · u) = u · t
        may-swap-app _ t       = t

module Tmᶠ&ᴮ where
    [_]? : ∀ {n} → Tmᴮ →? Tmᶠ n
    -- {{{
    [ V x   ]? = ⟪  V  ∙ fromℕ? _ x ⟫?
    [ ƛ t   ]? = ⟪  ƛ  ∙ [ t ]? ⟫?
    [ t · u ]? = ⟪ _·_ ∙ [ t ]? ∙ [ u ]? ⟫?
    -- }}}

    [_] : ∀ {n} → Tmᶠ n → Tmᴮ
    -- {{{
    [ V x   ] = V (Fin.toℕ x)
    [ t · u ] = [ t ] · [ u ]
    [ ƛ t   ] = ƛ [ t ]
    -- }}}

open Tmᶠ&ᴮ public renaming ([_]? to Tmᴮ⇒ᶠ?; [_] to Tmᶠ⇒ᴮ)

parseTmᶠ? : ∀ {n} → String →? Tmᶠ n
parseTmᶠ? s = Tmᴮ⇒ᶠ? =<<? parseTmᴮ? s

parseTmᶠ : ∀ {n} → T[ parseTmᶠ? {n} ]
parseTmᶠ =          F[ parseTmᶠ? ]

showTmᶠ : ∀ {n} → Tmᶠ n → String
showTmᶠ t = showTmᴮ (Tmᶠ⇒ᴮ t)

module SubstTmᶠ where
    _→™_ : ℕ → ℕ → Set
    i →™ o = Tmᶠ i → Tmᶠ o

    _⇶_ : ℕ → ℕ → Set
    -- {{{
    i ⇶ o = Fin i → Tmᶠ o
    -- }}}

    ⇑ : ∀ {i o} → i ⇶ o → suc i ⇶ suc o
    -- {{{
    ⇑ f zero    = V zero
    ⇑ f (suc x) = mapᶠ suc (f x)
    -- }}}

    [_] : ∀ {i o} → i ⇶ o → i →™ o
    -- {{{
    [ θ ](V x)   = θ x
    [ θ ](ƛ t)   = ƛ ([ ⇑ θ ] t)
    [ θ ](t · u) = [ θ ] t · [ θ ] u
    -- }}}

    0≔ : ∀ {n} → Tmᶠ n → suc n ⇶ n
    -- {{{
    0≔ u = Fin-elim u V
    -- }}}

    β-red : ∀ {n} → n →™ n
    β-red (ƛ t · u) = [ 0≔ u ] t
    β-red t         = t

    _>>=_ : ∀ {m n} → Tmᶠ m → (Fin m → Tmᶠ n) → Tmᶠ n
    t >>= f = [ f ] t

    _$ᶠ_ : ∀ {n} → Tmᶠ n → Tmᶠ n → Tmᶠ n
    ƛ t $ᶠ u = [ 0≔ u ] t
    t   $ᶠ u = t · u

    evalᶠ : ℕ → ∀ {n} → Tmᶠ n → Tmᶠ n
    evalᶠ zero    t       = t
    evalᶠ (suc n) (V x)   = V x
    evalᶠ (suc n) (t · u) = evalᶠ n (evalᶠ n t $ᶠ u)
    evalᶠ (suc n) (ƛ t)   = ƛ (evalᶠ n t)

apTmᶠ : Tmᶠ 0
apTmᶠ = ƛ (ƛ (V (# 1) · V (# 0)))

non-closedTmᶠ : Tmᶠ 1
non-closedTmᶠ = ƛ (V (# 1) · V (# 0))

Ωᶠ : ∀ {n} → Tmᶠ n
Ωᶠ = parseTmᶠ Ωˢ

-- }}}

{-
 _   _           _           _
| \ | | ___  ___| |_ ___  __| |
|  \| |/ _ \/ __| __/ _ \/ _` |
| |\  |  __/\__ \ ||  __/ (_| |
|_| \_|\___||___/\__\___|\__,_|

References:

* “Substitution: A Formal Methods Case Study
   Using Monads and Transformations”
  Françoise Bellegarde and James Hook
  1994

* “de Bruijn Notation as a Nested Datatype”
  Richard Bird and Ross Paterson
  1999

* “Monadic Presentations of Lambda Terms Using
   Generalized Inductive Types”
  Thorsten Altenkirch and Bernhard Reus
  1999
-}
-- {{{
-- Maybe  : Set → Set
-- Maybe^ : ℕ → Set → Set

_ᴹ : ∀ {a} {A : Set a} n → Maybe^ (suc n) A
zero  ᴹ = nothing
suc n ᴹ = just (n ᴹ)

data Tmᴹ A : Set where
  -- {{{
  V    : (x : A) → Tmᴹ A
  _·_  : (t u : Tmᴹ A) → Tmᴹ A
  ƛ    : (t : Tmᴹ (Maybe A)) → Tmᴹ A
  -- }}}

mapᴹ : ∀ {A B} → (A → B) → Tmᴹ A → Tmᴹ B
-- {{{
mapᴹ f (V x)   = V (f x)
mapᴹ f (t · u) = mapᴹ f t · mapᴹ f u
mapᴹ f (ƛ t)   = ƛ (mapᴹ (map? f) t)
-- }}}

{- Map laws (derivable from parametricity)
mapᴹ-lem :
    (f : ∀ {A} → Tmᴹ A → Tmᴹ A)
    → ∀ {A B} (g : A → B) → mapᴹ g ∘ f ≗ f ∘ mapᴹ g

mapᴹ-lem′ :
    (f : ∀ {A} → Tmᴹ A → Bool)
    → ∀ {A B} (g : A → B) → f ≗ f ∘ mapᴹ g
 -}

module Tmᶠ⇒ᴹ where
    [_] : ∀ {n} → Tmᶠ n → ∀ {A} → Tmᴹ (Maybe^ n A)
    -- {{{
    [ V x   ] = V (fromFin x)
    [ t · u ] = [ t ] · [ u ]
    [ ƛ t   ] = ƛ [ t ]
    -- }}}
open Tmᶠ⇒ᴹ renaming ([_] to Tmᶠ⇒ᴹ)

module Tmᴹ⇒ᶠ where
    [_] : ∀ {n} → Tmᴹ (Maybe^ n ⊥) → Tmᶠ n
    -- {{{
    [ V x   ] = V (toFin x)
    [ t · u ] = [ t ] · [ u ]
    [ ƛ t   ] = ƛ [ t ]
    -- }}}
open Tmᴹ⇒ᶠ renaming ([_] to Tmᴹ⇒ᶠ)

parseTmᴹ? : ∀ {A} → String →? Tmᴹ A
parseTmᴹ? s = map? (λ x → Tmᶠ⇒ᴹ {0} x) (parseTmᶠ? s)

parseTmᴹ : ∀ {A} → T[ parseTmᴹ? {A} ]
parseTmᴹ = F[ parseTmᴹ? ]

showTmᴹ : Tmᴹ ⊥ → String
showTmᴹ t = showTmᶠ (Tmᴹ⇒ᶠ {0} t)

Ωᴹ : ∀ {A} → Tmᴹ A
Ωᴹ = parseTmᴹ Ωˢ

module SubstTmᴹ where
    _⇶_ : Set → Set → Set
    -- {{{
    A ⇶ B = A → Tmᴹ B
    -- }}}

    _→™_ : Set → Set → Set
    -- {{{
    A →™ B = Tmᴹ A → Tmᴹ B
    -- }}}

    ⇑ : ∀ {A B} → A ⇶ B → Maybe A ⇶ Maybe B
    -- {{{
    ⇑ f nothing  = V nothing
    ⇑ f (just x) = mapᴹ just (f x)
    -- }}}

    [_] : ∀ {A B} → A ⇶ B → A →™ B
    -- {{{
    [ θ ](V x)   = θ x
    [ θ ](t · u) = [ θ ] t · [ θ ] u
    [ θ ](ƛ t)   = ƛ ([ ⇑ θ ] t)
    -- }}}

    0≔ : ∀ {A} → Tmᴹ A → Maybe A ⇶ A
    -- {{{
    0≔ = maybe V
    -- }}}

    -- {{{
    _>>=_ : ∀ {A B} → Tmᴹ A → (A → Tmᴹ B) → Tmᴹ B
    t >>= f = [ f ] t

    join : ∀ {A} → Tmᴹ (Tmᴹ A) → Tmᴹ A
    join = [ id ]

    β-red : ∀ {A} → Tmᴹ A → Tmᴹ A
    β-red (ƛ t · u) = [ 0≔ u ] t
    β-red t         = t

    _$ᴹ_ : ∀ {A} → Tmᴹ A → Tmᴹ A → Tmᴹ A
    ƛ t $ᴹ u = [ 0≔ u ] t
    t   $ᴹ u = t · u

    evalᴹ : ℕ → ∀ {A} → Tmᴹ A → Tmᴹ A
    evalᴹ zero    t       = t
    evalᴹ (suc n) (V x)   = V x
    evalᴹ (suc n) (t · u) = evalᴹ n (evalᴹ n t $ᴹ u)
    evalᴹ (suc n) (ƛ t)   = ƛ (evalᴹ n t)
    -- }}}
open SubstTmᴹ using (_$ᴹ_; evalᴹ) renaming ([_] to [_]ᴹ; 0≔ to 0ᴹ≔)

apTmᴹ : Tmᴹ ⊥
apTmᴹ = ƛ (ƛ (V (1 ᴹ) · V (0 ᴹ)))

non-closedTmᴹ : Tmᴹ (Maybe ⊥)
non-closedTmᴹ = ƛ (V (1 ᴹ) · V (0 ᴹ))

evalᴹˢ = λ s {pf} n → showTmᴹ (evalᴹ n (parseTmᴹ s {pf}))

data ⟦Tmᴹ⟧ {A₁ A₂} (Aᵣ : A₁ → A₂ → Set) : ⟦Set₀⟧ (Tmᴹ A₁) (Tmᴹ A₂) where
  ⟦V⟧    : (Aᵣ ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ) V V
  _⟦·⟧_  : (⟦Tmᴹ⟧ Aᵣ ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ) _·_ _·_
  ⟦ƛ⟧    : (⟦Tmᴹ⟧ (⟦Maybe⟧ Aᵣ) ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ) ƛ ƛ

-- Turn a function into a relation
⟨_⟩ᴿ : ∀ {A B : Set} → (A → B) → A → B → Set
⟨ f ⟩ᴿ x y = f x ≡ y

map?⇒⟦Maybe⟧ : ∀ {A B : Set} (f : A → B) → ⟨ map? f ⟩ᴿ ⇒ ⟦Maybe⟧ ⟨ f ⟩ᴿ
map?⇒⟦Maybe⟧ f {just x}  ≡.refl = ⟦just⟧ ≡.refl
map?⇒⟦Maybe⟧ f {nothing} ≡.refl = ⟦nothing⟧

⟦Maybe⟧⇒map? : ∀ {A B} (f : A → B) → ⟦Maybe⟧ ⟨ f ⟩ᴿ ⇒ ⟨ map? f ⟩ᴿ
⟦Maybe⟧⇒map? f (⟦just⟧ ≡.refl) = ≡.refl
⟦Maybe⟧⇒map? f ⟦nothing⟧       = ≡.refl

⟦Maybe⟧-⇒ : ∀ {A₁ A₂ : Set} {Aᵣ Aᵣ′ : A₁ → A₂ → Set} (Aᵣ⇒Aᵣ′ : Aᵣ ⇒ Aᵣ′)
            → ⟦Maybe⟧ Aᵣ ⇒ ⟦Maybe⟧ Aᵣ′
⟦Maybe⟧-⇒ Aᵣ⇒Aᵣ′ (⟦just⟧ pf) = ⟦just⟧ (Aᵣ⇒Aᵣ′ pf)
⟦Maybe⟧-⇒ _      ⟦nothing⟧  = ⟦nothing⟧

⟦Tmᴹ⟧-⇒ : ∀ {A₁ A₂ : Set} {Aᵣ Aᵣ′ : A₁ → A₂ → Set}
                → Aᵣ ⇒ Aᵣ′
                → ⟦Tmᴹ⟧ Aᵣ ⇒ ⟦Tmᴹ⟧ Aᵣ′
-- {{{
⟦Tmᴹ⟧-⇒ Aᵣ⇒Aᵣ′ (⟦V⟧ xᵣ) = ⟦V⟧ (Aᵣ⇒Aᵣ′ xᵣ)
⟦Tmᴹ⟧-⇒ Aᵣ⇒Aᵣ′ (tᵣ ⟦·⟧ uᵣ) = ⟦Tmᴹ⟧-⇒ Aᵣ⇒Aᵣ′ tᵣ ⟦·⟧ ⟦Tmᴹ⟧-⇒ Aᵣ⇒Aᵣ′ uᵣ
⟦Tmᴹ⟧-⇒ Aᵣ⇒Aᵣ′ (⟦ƛ⟧ tᵣ) = ⟦ƛ⟧ (⟦Tmᴹ⟧-⇒ (⟦Maybe⟧-⇒ Aᵣ⇒Aᵣ′) tᵣ)
-- }}}

module ⟦Tmᴹ⟧⇔mapᴹ where
    [_] : ∀ {A B} (f : A → B) (t : Tmᴹ A) → ⟦Tmᴹ⟧ ⟨ f ⟩ᴿ t (mapᴹ f t)
    -- {{{
    [ f ](V x)   = ⟦V⟧ ≡.refl
    [ f ](t · u) = [ f ] t ⟦·⟧ [ f ] u
    [ f ](ƛ t)   = ⟦ƛ⟧ (⟦Tmᴹ⟧-⇒ (map?⇒⟦Maybe⟧ f) ([ map? f ] t))
    -- }}}

    [_]' : ∀ {A B} (f : A → B) → ⟦Tmᴹ⟧ ⟨ f ⟩ᴿ ⇒ ⟨ mapᴹ f ⟩ᴿ
    -- {{{
    [ f ]' (⟦V⟧ ≡.refl) = ≡.refl
    [ f ]' (t ⟦·⟧ u)
      rewrite [ f ]' t
            | [ f ]' u
            = ≡.refl
    [ f ]' (⟦ƛ⟧ t)
      rewrite [ map? f ]' (⟦Tmᴹ⟧-⇒ (⟦Maybe⟧⇒map? f) t)
            = ≡.refl
    -- }}}

    mapᴹ⇒⟦Tmᴹ⟧ : ∀ {A B} (f : A → B) → ⟨ mapᴹ f ⟩ᴿ ⇒ ⟦Tmᴹ⟧ ⟨ f ⟩ᴿ
    mapᴹ⇒⟦Tmᴹ⟧ f {t} ≡.refl = [ f ] t

    ⟦Tmᴹ⟧⇒mapᴹ : ∀ {A B} (f : A → B) → ⟦Tmᴹ⟧ ⟨ f ⟩ᴿ ⇒ ⟨ mapᴹ f ⟩ᴿ
    ⟦Tmᴹ⟧⇒mapᴹ f = [ f ]'

module Tmᴹ-param where
    open ⟦Tmᴹ⟧⇔mapᴹ

    thm : (f : ∀ {A} → Tmᴹ A → Tmᴹ A)
          (fᵣ : (∀⟨ Aᵣ ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦Tmᴹ⟧ Aᵣ ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ) f f)
          {A B : Set}
          (g : A → B)
          → mapᴹ g ∘ f ≗ f ∘ mapᴹ g
    thm f fᵣ g x = ⟦Tmᴹ⟧⇒mapᴹ g (fᵣ ⟨ g ⟩ᴿ (mapᴹ⇒⟦Tmᴹ⟧ g ≡.refl))

    thm2 : (f : ∀ {A} → Tmᴹ A → Bool)
           (fᵣ : (∀⟨ Aᵣ ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦Tmᴹ⟧ Aᵣ ⟦→⟧ ⟦Bool⟧) f f)
           {A B : Set}
           (g : A → B)
           → f ≗ f ∘ mapᴹ g
    thm2 f fᵣ g x = ⟦Bool⟧⇒≡ (fᵣ ⟨ g ⟩ᴿ (mapᴹ⇒⟦Tmᴹ⟧ g ≡.refl))

    ⟦Cmp⟧ : (⟦Set₀⟧ ⟦→⟧ ⟦Set₀⟧) Cmp Cmp
    ⟦Cmp⟧ Aᵣ = Aᵣ ⟦→⟧ Aᵣ ⟦→⟧ ⟦Bool⟧

    thm3 : (f : ∀ {A} → Cmp A → Tmᴹ A → Tmᴹ A)
           (fᵣ : (∀⟨ Aᵣ ∶ ⟦Set₀⟧ ⟩⟦→⟧ ⟦Cmp⟧ Aᵣ ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ ⟦→⟧ ⟦Tmᴹ⟧ Aᵣ) f f)
           {A₁ A₂ : Set}
           (cmp₁ : Cmp A₁)
           (cmp₂ : Cmp A₂)
           (g : A₁ → A₂)
           (g-ok : ∀ {x₁ y₁} → cmp₁ x₁ y₁ ≡ cmp₂ (g x₁) (g y₁))
          → mapᴹ g ∘ f cmp₁ ≗ f cmp₂ ∘ mapᴹ g
    thm3 f fᵣ cmp₁ cmp₂ g g-ok x =
      ⟦Tmᴹ⟧⇒mapᴹ g (fᵣ ⟨ g ⟩ᴿ pf (mapᴹ⇒⟦Tmᴹ⟧ g ≡.refl))
      where pf : ∀ {x₁ x₂} → g x₁ ≡ x₂ →
                 ∀ {y₁ y₂} → g y₁ ≡ y₂ →
                   ⟦Bool⟧ (cmp₁ x₁ y₁) (cmp₂ x₂ y₂)
            pf ≡.refl ≡.refl = ⟦Bool⟧-Props.reflexive g-ok

-- }}}

{-
 ____  _   _  ___    _    ____
|  _ \| | | |/ _ \  / \  / ___|
| |_) | |_| | | | |/ _ \ \___ \
|  __/|  _  | |_| / ___ \ ___) |
|_|   |_| |_|\___/_/   \_\____/

References:
* “Higher-Order Abstract Syntax in Coq”
  Joëlle Despeyroux, Amy Felty, and André Hirschowitz
  1995

* “Semantical Analysis of Higher-Order Abstract Syntax”
  Martin Hofmann
  1999

* “Parametric higher-order abstract syntax for mechanized semantics”
  Adam Chlipala
  2008
-}
-- {{{

data Tmᴾ (Var : Set) : Set where
  -- {{{
  V   : (v : Var) → Tmᴾ Var
  _·_ : (t u : Tmᴾ Var) → Tmᴾ Var
  ƛ   : (f : Var → Tmᴾ Var) → Tmᴾ Var
  -- }}}

-- Closed PHOAS terms (terms with 0 free variables)
Tmᴾ₀ : Set₁
Tmᴾ₀ = ∀ {Var} → Tmᴾ Var

-- Abstractions (PHOAS terms with at most 1 free variable)
Tmᴾ₁ : Set₁
Tmᴾ₁ = ∀ {Var} → Var → Tmᴾ Var

joinᴾ : ∀ {Var} → Tmᴾ (Tmᴾ Var) → Tmᴾ Var
joinᴾ (V t)     = t
joinᴾ (t · u)   = joinᴾ t · joinᴾ u
joinᴾ (ƛ f)     = ƛ (λ x → joinᴾ (f (V x)))

-- Substitution function
[_]ᴾ : Tmᴾ₁ → Tmᴾ₀ → Tmᴾ₀
[ t ]ᴾ u = joinᴾ (t u)

idTmᴾ₀ : Tmᴾ₀
idTmᴾ₀ = ƛ V

apTmᴾ₀ : Tmᴾ₀
apTmᴾ₀ = ƛ λ f → ƛ λ x → V f · V x

β-redᴾᴾ : ∀ {A} → Tmᴾ (Tmᴾ A) → Tmᴾ (Tmᴾ A)
β-redᴾᴾ (ƛ f · t) = f (joinᴾ t)
β-redᴾᴾ t         = t

β-redᴾ : Tmᴾ₀ → Tmᴾ₀
β-redᴾ t = joinᴾ (β-redᴾᴾ t)

module Tmᴹ⇔ᴾ where
    [_] : ∀ {A B} → (A → B) → Tmᴹ A → Tmᴾ B
    [ f ](V x)   = V (f x)
    [ f ](t · u) = [ f ] t · [ f ] u
    [ f ](ƛ t)   = ƛ λ x → [ maybe f x ] t

    Tmᴹ⇒ᴾ : ∀ {A} → Tmᴹ A → Tmᴾ A
    Tmᴹ⇒ᴾ t = [ id ] t

    Tmᴹ⇒ᴾ₀ : Tmᴹ ⊥ → Tmᴾ₀
    Tmᴹ⇒ᴾ₀ t = [ ⊥-elim ] t

open Tmᴹ⇔ᴾ public using (Tmᴹ⇒ᴾ; Tmᴹ⇒ᴾ₀)

parseTmᴾ? : String →? Tmᴾ₀
parseTmᴾ? s = map? Tmᴹ⇒ᴾ₀ (parseTmᴹ? s)

parseTmᴾ : T[ parseTmᴾ? ]
parseTmᴾ = F[ parseTmᴾ? ]

module Tmᴾ⇒ᴮ where
    [_] : ℕ → Tmᴾ ℕ → Tmᴮ
    -- {{{
    [ ℓ ](V x  ) = V x
    [ ℓ ](t · u) = [ ℓ ] t · [ ℓ ] u
    [ ℓ ](ƛ t  ) = ƛ ([ 1 + ℓ ] (t ℓ))
    -- }}}

    Tmᴾ₀⇒ᴮ : Tmᴾ₀ → Tmᴮ
    Tmᴾ₀⇒ᴮ t = [ 0 ] t

open Tmᴾ⇒ᴮ public renaming ([_] to Tmᴾ⇒ᴮ)

showTmᴾ : Tmᴾ₀ → String
showTmᴾ t = showTmᴮ (Tmᴾ₀⇒ᴮ t)

1-β-redᴾ : ∀ s → {pf : just? (parseTmᴾ? s)} → String
1-β-redᴾ s {pf} = showTmᴾ (β-redᴾ (parseTmᴾ s {pf}))

-- }}}

{-
 ____              _                __              _____
/ ___| _   _ _ __ | |_ __ ___  __  / _| ___  _ __  |  ___| __ ___  ___
\___ \| | | | '_ \| __/ _` \ \/ / | |_ / _ \| '__| | |_ | '__/ _ \/ _ \
 ___) | |_| | | | | || (_| |>  <  |  _| (_) | |    |  _|| | |  __/  __/
|____/ \__, |_| |_|\__\__,_/_/\_\ |_|  \___/|_|    |_|  |_|  \___|\___|
       |___/

Reference:
  “Syntax for free: representing syntax with binding
   using parametricity”
  Robert Atkey
  2009
-}
-- {{{

-- Open HOAS terms
Tmᴴ : Set → Set
Tmᴴ A = (lam : (A → A) → A) →
        (app : A → A → A) → A

-- Close HOAS terms
Tmᴴ₀ : Set₁
Tmᴴ₀ = ∀ {A} → Tmᴴ A

Tmᴴᴾ⇒ᴾ : ∀ {A} → Tmᴴ (Tmᴾ A) → Tmᴾ A
Tmᴴᴾ⇒ᴾ t = t (λ f → ƛ (f ∘ V)) _·_

Tmᴴ⇒ᴾ₀ : Tmᴴ₀ → Tmᴾ₀
Tmᴴ⇒ᴾ₀ t = Tmᴴᴾ⇒ᴾ t

Tmᴴ₀⇒ᴮ : Tmᴴ₀ → Tmᴮ
Tmᴴ₀⇒ᴮ t = t {ℕ → Tmᴮ} lam app 0
  where
    lam = λ f i → ƛ (f (λ j → V (j ∸ suc i)) (suc i))
    app = λ x y i → x i · y i

module Tmᴾ⇒ᴴ {A : Set} (lam : (A → A) → A) (app : A → A → A) where
  [_] : Tmᴾ A → A
  [ V v   ] = v
  [ t · u ] = app [ t ] [ u ]
  [ ƛ f   ] = lam (λ x → [ f x ])

Tmᴾ⇒ᴴ : ∀ {A : Set} → Tmᴾ A → Tmᴴ A
Tmᴾ⇒ᴴ t lam app = Tmᴾ⇒ᴴ.[_] lam app t

Tmᴾ⇒ᴴ₀ : Tmᴾ₀ → Tmᴴ₀
Tmᴾ⇒ᴴ₀ t = Tmᴾ⇒ᴴ t

Tmᴹ⇒ᴴ : ∀ {A} → Tmᴹ A → Tmᴴ A
Tmᴹ⇒ᴴ = Tmᴾ⇒ᴴ ∘ Tmᴹ⇒ᴾ

Tmᴹ⇒ᴴ₀ : Tmᴹ ⊥ → Tmᴴ₀
Tmᴹ⇒ᴴ₀ = Tmᴾ⇒ᴴ₀ ∘ Tmᴹ⇒ᴾ₀

idTmᴴ : Tmᴴ₀
idTmᴴ lam app = lam id

apTmᴴ : Tmᴴ₀
apTmᴴ lam app = lam λ f → lam λ x → app f x

parseTmᴴ? : String →? Tmᴴ₀
parseTmᴴ? s = map? Tmᴾ⇒ᴴ₀ (parseTmᴾ? s)

parseTmᴴ = F[ parseTmᴴ? ]

showTmᴴ : Tmᴴ₀ → String
showTmᴴ t = showTmᴾ (Tmᴴ⇒ᴾ₀ t)

roundᴴ : ∀ s → {pf : just? (parseTmᴴ? s)} → String
roundᴴ s {pf} = showTmᴴ (parseTmᴴ s {pf})

test : 1-β-redᴾ Ωˢ ≡ Ωˢ
test = ≡.refl

-- }}}

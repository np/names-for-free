open import Level
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)
open import Function

_~′_ : ∀ {a b} {A : Set a} {B : A → Set b} (f g : (x : A) → B x) → Set(a ⊔ b)
f ~′ g = ∀ x → f x == g x

ap2 : ∀ {a b c : Set} {x1 x2 : a} {y1 y2 : b} -> (f : a -> b -> c) -> (x1 == x2) -> (y1 == y2) -> f x1 y1 == f x2 y2
ap2 f refl refl = refl


Type = Set
Type1 = Set1


… : ∀ {a} {A : Set a} {{x : A}} → A
… {{x}} = x

data Zero : Type where

data Bool : Type where
  true false : Bool

record One : Type where
  constructor tt

data _⊎_ (A : Type)(B : Type) : Type where
  left : A → A ⊎ B
  right : B → A ⊎ B

map⊎ : ∀{A B C D} -> (A -> C) -> (B -> D) -> A ⊎ B -> C ⊎ D
map⊎ f g (left x) = left (f x)
map⊎ f g (right x) = right (g x)

elim⊎ : ∀{A B} {C : Set} -> (A -> C) -> (B -> C) -> A ⊎ B -> C
elim⊎ f g (left x) =  (f x)
elim⊎ f g (right x) = (g x)

Π : (A : Type) (B : A → Type) → Type
Π A B = (x : A) → B x

record Σ (A : Type) (B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
open  Σ
_×_ = \A B -> Σ A (\_ -> B)

pair= : ∀ {A} {B : A → Type} {p q : Σ A B} (e : fst p == fst q) → tr B e (snd p) == snd q → p == q
pair= {p = fst , snd} {.fst , snd₁} refl eq = cong (_,_ fst) eq

-- Assumes K.
-- TODO: makes the K assumption explicit and make
-- the proper proof term.
ap-snd : ∀ {A : Type} {B : A → Type}
           {x : A} {y z : B x}
         → _==_ {A = Σ A B} (x , y) (x , z) → y == z
ap-snd refl = refl

World = Type -- a context of names


-- Question: is it possible to "break" the system if Binder is made concrete as follows?
-- NP: First, as soon as ♦/fresh exist then the function Stupid.swp type-checks
-- with only abstract binders we won't be able to write both w ▹ b ▹ b' and w ▹ b' ▹ b
-- Second this concrete representation for Binder brings binder-uniq/binder-♦ which
-- I think is harmless in the current setting.
-- In particular terms are monadic even when Binder is kept abstract.

-- JP:
-- Keeping ♦ abstract makes us remain safe; in the sense that we can never confuse two binders.
-- One way to explain it: NablaP and NablaS are both safe (static) name introducers/eliminers.
-- But "NablaF" allows to manipulate names without having a static handle on their binder.
-- It is ok as long as each instance of ◆ is considered different from another. But not otherwise.

-- However, making ♦ concrete (and a single value) allows to compute.
-- Computationally, this corresponds to the unification of NablaP and
-- NablaS, (eg. like the erasure semantics that we have outlined.)

-- Maybe there is a simple way to make Agda support the semantics that we want?



-- type of a binder fresh for w. ('b:Binder w' could be written 'b FreshFor w')
-- data Binder (w : World) : Set where
--   ♦ : Binder w

-- JP: THIS IS BAAAD (see remark on safety above)
-- NP: ...but this is derivable :) see binder-uniq' below
-- binder-uniq : ∀ {w} (b₀ b₁ : Binder w) → b₀ == b₁
-- binder-uniq ♦ ♦ = refl

-- binder-♦ : ∀ {w} (b : Binder w) → b == ♦
-- binder-♦ ♦ = refl

postulate
  Binder : (w : World) → Set
  ♦ : ∀ {w} → Binder w

NablaP : ∀ w → (T : Binder w → Set) → Set
NablaP = λ w T → Π (Binder w) T

NablaS : ∀ w → (T : Binder w → Set) → Set
NablaS = λ w T → Σ (Binder w) T

NablaF : ∀ w → (T : Binder w → Set) → Set
NablaF = λ w T → T ♦

module _ {w : World} (T : Binder w → Type) where
    -- Scopes -- Representations of ∇(b∉w). T[b]
    -- pack : NablaP w T → NablaS w T
    -- pack f = ♦ , f ♦

    -- unpack : NablaS w T → NablaP w T
    -- unpack (♦ , t) ♦ = t

    FS : NablaF w T → NablaS w T
    FS x = ♦ , x

    postulate
      SF : NablaS w T → NablaF w T
    -- SF = {!!} -- SF (♦ , t) = t

    postulate
      FP : NablaF w T → NablaP w T
    -- FP = {!!} -- FP x ♦ = x

    PF : NablaP w T → NablaF w T
    PF x = x ♦

fresh : ∀ w -> Binder w
fresh _ = ♦

infixl 5 _▹_
data _▹_ (w : World) : (b : Binder w) -> Type where
  old : {b : Binder w} -> w → w ▹ b
  new : (b : Binder w) -> w ▹ b


module Derived-from-PS-SP
    (PS : {w : World} (T : Binder w → Set) → NablaP w T → NablaS w T)
    (SP : {w : World} (T : Binder w → Set) → NablaS w T → NablaP w T)
    where

    fresh' : ∀ w → Binder w
    fresh' w = fst (PS (_▹_ w) new)

    ♦' : ∀ {w} → Binder w
    ♦' = fresh' _

    NablaF' : ∀ w → (T : Binder w → Set) → Set
    NablaF' w T = T ♦'

    FS' : {w : World} (T : Binder w → Set) → NablaF' w T → NablaS w T
    FS' T t = ♦' , t

    PF' : {w : World} (T : Binder w → Set) → NablaP w T → NablaF' w T
    PF' T f = f ♦'

    SF' : {w : World} (T : Binder w → Set) → NablaS w T → NablaF' w T
    SF' T = PF' T ∘ SP T

    FP' : {w : World} (T : Binder w → Set) → NablaF' w T → NablaP w T
    FP' T = SP T ∘ FS' T

    binder-♦' : ∀ {w} (b : Binder w) → b == ♦'
    binder-♦' = FP' _ refl

    binder-uniq' : ∀ {w} (b₀ b₁ : Binder w) → b₀ == b₁
    binder-uniq' = FP' _ (FP' _ refl)
       -- I could use binder-♦' twice but this FP' awesome :)

    -- should be easy
    {-
    binder-K : ∀ {w} (b : Binder w) (p : b == b) → p == refl
    binder-K = FP' _ λ p → {!!}
    -}

    FS'-inj : {w : World} (T : Binder w → Set)
              {x y : NablaF' w T} → FS' T x == FS' T y → x == y
    FS'-inj _ e = ap-snd e -- TODO pass binder-K

    NablaS= : {w : World} (T : Binder w → Set)
              {x y : NablaS w T} → tr T (binder-uniq' _ _) (snd x) == snd y → x == y
    NablaS= T = pair= (binder-uniq' _ _)

    NablaSP= : {{_ : FunExt}}
               {w : World} (T : Binder w → Set)
               {f g : NablaP w T} → (NablaS w λ b → f b == g b) → f == g
    NablaSP= _ e = λ= (SP _ e)

    unpack2S : {r : Set} {w : World} (T : Binder w → Set)
               (t₀ t₁ : NablaS w T)
               (k : ∀ v → (u₀ u₁ : T v) → r) → r
    unpack2S T (b₀ , t₀) t₁ k = k b₀ t₀ (SP T t₁ b₀)

    unpack2SF : {r : Set} {w : World} (T : Binder w → Set)
                (t₀ t₁ : NablaS w T)
                (k : (u₀ u₁ : T ♦') → r) → r
    unpack2SF T t₀ t₁ k = k (SF' T t₀) (SF' T t₁)

    {-
    ap-snd′ : ∀ {w} {T : Binder w → Type}
               {x y : NablaS w T}
               (p : x == y) → tr T (binder-uniq' _ _) (snd x) == snd y
    ap-snd′ p = {!!}

    SF'-inj' : {w : World} (T : Binder w → Set)
              {x y : NablaS w T} → SF' T x == SF' T y → x == y
    SF'-inj' T e = pair= (binder-uniq' _ _) {!!}

    PS-inj : {{_ : FunExt}}
             {w : World} (T : Binder w → Set)
             {f g : NablaP w T} → PS T f == PS T g → f == g
    PS-inj T e = λ= (SP _ (♦' , {!!}))
    -}

    module _
      (SP-inj : {w : World} (T : Binder w → Set)
                {x y : NablaS w T} → SP T x == SP T y → x == y)
      {-
      (PS-inj : {w : World} (T : Binder w → Set)
                {f g : NablaP w T} → PS T f == PS T g → f == g)
      -}
      {{_ : FunExt}}
      where

        SP-inj' : {w : World} (T : Binder w → Set)
                  {x y : NablaS w T} → SP T x ~′ SP T y → x == y
        SP-inj' T e = SP-inj T (λ= e)

        SF'-inj : {w : World} (T : Binder w → Set)
                  {x y : NablaS w T} → SF' T x == SF' T y → x == y
        SF'-inj T = SP-inj' T ∘ FP' _



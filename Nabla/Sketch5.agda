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

record Functor (F : Set -> Set) : Set1 where
  infixl 4 _<$>_
  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B
  map = _<$>_
  field
    <$>-id : ∀ {α}{f : α → α} (pf : f ~ id) → _<$>_ f ~ id
    <$>-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ}
            (h= : f ∘ g ~ h)
          → map f ∘ map g ~ map h

record Monad (M : Set -> Set) : Set1 where
  -- Kleisli arrow
  _→K_ : Set -> Set -> Set
  _→K_ A B = A → M B
  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

  subs : ∀ {A B} → (A → M B) → M A  → M B
  subs = λ x x₁ → x₁ >>= x

  join : ∀ {A} -> M (M A) -> M A
  join x = x >>= id

  -- Kleisli composition
  _∘k_ : ∀ {α β γ} (s : β →K γ) (s' : α →K β) → α →K γ
  _∘k_ s s' x = subs s (s' x)

  field
    bind-assoc : ∀ {α β γ} {s : β →K γ} {s' : α →K β} {s'' : α →K γ} (s= : (s ∘k s') ~ s'') → subs s ∘ subs s' ~ subs s''
    right-id : ∀ {α}{s} (s= : s ~ return) → subs {α} s ~ id
    left-id : ∀ {α β x} {f : α →K β} -> return x >>= f == f x

  instance
    functor : Functor M
    functor = record { _<$>_ = λ f m → m >>= (λ x → return (f x))
                     ; <$>-id = λ pf → right-id (λ x₁ → ap return (pf x₁))
                     ; <$>-∘ = λ h= → bind-assoc (λ x₁ → trans left-id (ap return (h= x₁))) }
  -- open Functor functor public

module _ {F : Set -> Set} {{F : Monad F}} where
  open Monad F public
module _ {F : Set -> Set} {{F : Functor F}} where
  open Functor F public

Type = Set
Type1 = Set1

-- Grph : ∀ {A B : Type} (f : A → B) → A → B → Type
-- Grph f x y = f x == y

-- _⇒_ : ∀ {A B : Type} (R S : A → B → Type) → Type
-- R ⇒ S = ∀ {x y} → R x y → S x y

… : ∀ {a} {A : Set a} {{x : A}} → A
… {{x}} = x

data Zero : Type where

data Bool : Type where
  true false : Bool

record One : Type where
  constructor tt

-- T : Bool -> Type
-- T true = One
-- T false = Zero

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

◆ : ∀ {w} → Binder w
◆ = ♦ 

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

{-
data The {w : World} : Binder w → Set where
  the : ∀ (b : Binder w) → The b

_▹_ : (w : World) (b : Binder w) → Type
w ▹ b = w ⊎ The b
pattern old w = left w
pattern new b = right (the b)
-}

-- World extended with a fresh variable.
_⇑ : (w : World) → World
w ⇑ = w ▹ ♦

-- b # v and b' # w
map▹  : ∀ {v w} b b' -> (v → w) → (v ▹ b) → (w ▹ b')
map▹ _ _ f (old x) = old (f x)
map▹ _ _ f (new ._) = new _

-- Map to a fresh thing
map⇑  : ∀ {v w} -> (v → w) → (v ⇑) → (w ⇑)
map⇑ = map▹ ♦ ♦

map▹-id : ∀ {α}{f : α → α} (pf : f ~ id){b} → map▹ b b f ~ id
map▹-id pf (old x) = ap old (pf x)
map▹-id pf (new _) = refl

module _ {α β γ}{f : β → γ}{g : α → β}{h : α → γ}(h= : f ∘ g ~ h) where
    map▹-∘ : ∀ b0 b1 b2 → map▹ b1 b2 f ∘ map▹ b0 b1 g ~ map▹ b0 b2 h
    map▹-∘ b0 b1 b2 (old x) = ap old (h= x)
    map▹-∘ b0 b1 b2 (new .b0) = refl

    map⇑-∘ : map⇑ f ∘ map⇑ g ~ map⇑ h
    map⇑-∘ = map▹-∘ _ _ _

mkScope : ∀ {w} (T : World -> Set) -> Binder w -> Set
mkScope {w} T = λ b → T (w ▹ b)

ScopeP : (T : World → Set) → World → Set
ScopeP = λ T w → NablaP w (mkScope T)

ScopeS : (T : World → Set) → World → Set
ScopeS = λ T w → NablaS w (mkScope T)

ScopeF : (T : World → Set) → World → Set
ScopeF = λ T w → NablaF w (mkScope T)

ScopeFFunctor : ∀ {F} -> Functor F -> Functor (ScopeF F)
ScopeFFunctor F = record { _<$>_ = λ f s →  map⇑ f <$> s
                         ; <$>-id = λ pf → <$>-id (map▹-id pf)
                         ; <$>-∘ = λ h= → <$>-∘ (map⇑-∘ h=) }

pack : {w : World} (T : World → Set) → ScopeP T w → ScopeF T w
pack {w} T x = x ♦

unpack : {r : Set} {w : World} (T : World → Set) → ScopeF T w → (∀ v -> T (w ▹ v) -> r) -> r
unpack = λ {r} {w} T₁ z z₁ → z₁ ♦ z

atVar : {w : World} (T : World → Set) → ScopeF T w → ScopeP T w
atVar T = FP (mkScope T)



{-
unpackPackScope : ∀ {w : World}  T (g : ScopeP T w) -> g == unpackScope T (packScope T g)
unpackPackScope T g = {!!} -- assumption

sndPack' : ∀ {w : World}  T (g : ScopeP T w) ->
           g _  ==  snd (packScope T g)
sndPack' T g = {!!}  -- unpackPackScope + injective pairs

sndPack : ∀ {w : World}  T (g : ScopeP T w) -> (P : T (w ▹ _) -> Set) ->
           P (g _)  -> P  (snd (packScope T g))
sndPack T g P p = {!tr sndPack'!}
-}
    -- Alternative is to use an abstract scope (Nabla) as actual representation; possibly more accurate than both the above.
      -- Nabla : ∀ w → (T : Binder w → Set) → Set
      -- toPi   : ∀ {w T} -> Nabla w T -> Π(Binder w) T
      -- fromPi : ∀ {w T} -> Π(Binder w) T -> Nabla w T 
      -- etc.


    -- no  need for the empty world; we can quantify on all worlds.

-- refer a specific binder
name : ∀ {w} → (b : Binder w) → w ▹ b
name b = new _

exportN : ∀ {α b} → (n : α ▹ b) → (name b == n) ⊎ α
exportN (old x) = right x
exportN (new _) = left refl

exportN-name : ∀ {α} (b : Binder α) → exportN (name b) == left refl
exportN-name b = refl

record _⇉_ (α β : World) : Set where
  constructor mk⇉
  field
    wkN : α → β
open _⇉_ public

atVar' : {α β : World} (T : World → Set) -> {{_ : Functor T}} → ScopeF T α -> (b : Binder β) → {{_ : α ⇉ β}} -> T (β ▹ b)
atVar' T {{Fun}} sc b {{mk⇉ s}} = map▹ _ _ s <$> sc

instance
  ⇉-skip :  ∀ {α β} {b} → {{s : α ⇉ β}} → α ⇉ ( β ▹ b )
  ⇉-skip {{mk⇉ s}} = mk⇉ (λ x → old (s x))

  ⇉-refl : ∀ {w} → w ⇉ w
  ⇉-refl = mk⇉ λ x → x

  -- ⇉-▹ :  ∀ {α β}{{s : α ⇉ β}} → (α ▹ ♦) ⇉ (β ▹ ♦)
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x -> map▹ ♦ ♦ s x

  -- ⇉-▹ :  ∀ {α β}{b}{b'}{{s : α ⇉ β}} → (α ▹ b) ⇉ (β ▹ b')
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ _ s x

  {- not sure on how instance arguments

  ⇉-▹ :  ∀ {α β}{b}{{s : α ⇉ β}}{{b'}} → (α ▹ b) ⇉ (β ▹ b')
  ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ s x
  -}

wkN' : ∀ {α β} {{s : α ⇉ β}} → α → β
wkN' = wkN …

_∈_ : ∀ {w}(b : Binder w)(w' : World) → Set
b ∈ w' = (_ ▹ b) ⇉ w'

name' : ∀ {w w'}(b : Binder w) {{s : b ∈ w'}} → w'
name' b = wkN' (name b)

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

{-
PS : {w : World} (T : Binder w → Set) → NablaP w T → NablaS w T
PS = {!!}
-- PS {w} T f = let ⟪ y , t ⟫ = ν x. f @ x in (y , t)

SP : {w : World} (T : Binder w → Set) → NablaS w T → NablaP w T
SP = {!!}
-- SP {w} T (x , t) y = ⟪ x , t ⟫ @ y
-}

subst0 : ∀ {M} {{Mon : Monad M}} {α b} → M α → (α ▹ b) →K α
subst0 u (old x) = return x
subst0 u (new ._)     = u

substituteOut : ∀ {M} {{Mon : Monad M}} {a} v ->  M a -> M (a ▹ v) -> M a
substituteOut {{Mon}} x t u = u >>= subst0 t

wk : ∀ {α β T} {{Fun : Functor T}} {{s : α ⇉ β}} → T α → T β
wk {{Fun}} = _<$>_ wkN'

liftSubst : ∀ {M} {{Mon : Monad M}} {a b v} {v' : Binder b} → a →K b → (a ▹ v) →K (b ▹ v')
liftSubst θ (old x) = wk (θ x)
liftSubst θ (new x) = return (new _)



module Stupid {w : World} where
  -- Both swp and id have the same type...

  swp : w ⇑ ⇑ → w ⇑ ⇑
  swp (old (old x)) = old (old x)
  swp (old (new ._)) = new _
  swp (new ._) = old (new _)

  swp' : ∀ {b : Binder w} {b' : Binder (w ▹ b)} -> w ▹ b ▹ b' → w ▹ b ▹ b'
  swp' (old (old x)) = old (old x)
  swp' {b} {b'} (old (new .b)) = new b'
  swp' {b} {b'} (new .b') = old (new b)


   
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

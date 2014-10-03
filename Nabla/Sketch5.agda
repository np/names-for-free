open import Level.NP
open import Data.Nat.NP hiding (_⊔_; _==_)
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

record Box {a} (A : Set a) : Set a where
  constructor box
  field unbox : A
open Box public

World = Type -- a context of names


data Binder (w : World) : Set where
  ♦ : Binder w

pattern ◆ = ♦

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

    SF : NablaS w T → NablaF w T
    SF (♦ , snd) = snd 

    FP : NablaF w T → NablaP w T
    FP x ♦ = x

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

-- World extended with an anonymous fresh variable.
_⇑ : (w : World) → World
w ⇑ = w ▹ ♦

infixl 5 _⇑^_

_⇑^_ : World → ℕ → World
w ⇑^ zero  = w
w ⇑^ suc n = (w ⇑^ n)⇑

old^ : ∀ {w} (n : ℕ) → w → w ⇑^ n
old^ zero    = id
old^ (suc n) = old ∘ old^ n

module _ {α β : World} where
    -- b # α and b' # β
    map▹  : ∀ b b' -> (α → β) → (α ▹ b) → (β ▹ b')
    map▹ _ _ f (old x) = old (f x)
    map▹ _ _ f (new ._) = new _

    -- Map to a fresh thing
    map⇑  : (α → β) → (α ⇑) → (β ⇑)
    map⇑ = map▹ ♦ ♦

map⇑^ : ∀ n {α β} → (α → β) → α ⇑^ n → β ⇑^ n
map⇑^ zero    = id
map⇑^ (suc n) = map⇑ ∘ map⇑^ n

{-
compose^ : ∀ n {α β} -> (α → β) → α ⇑^ n → β ⇑^ n
compose^ n = ?

foo : ∀ n {α} → map⇑ {α} (old^ n) ~ map⇑^ n old
foo n x = ?

foo : ∀ n {α} → map⇑^ n {α} old ~ map⇑^ old ∘ ?
foo zero x = {!!}
foo (suc n) (old x) = {!!}
foo (suc n) (new .♦) = {!!}
-}

module _ {α : World} where
    map▹-id : ∀ {f : α → α} (pf : f ~ id){b} → map▹ b b f ~ id
    map▹-id pf (old x) = ap old (pf x)
    map▹-id pf (new _) = refl

    map▹-id' : ∀ {b} → map▹ b b id ~ id
    map▹-id' = map▹-id λ _ → refl

    map⇑-id : ∀ {f : α → α} (pf : f ~ id) → map⇑ f ~ id
    map⇑-id pf = map▹-id pf {♦}

    map⇑-id' : map⇑ id ~ id
    map⇑-id' = map▹-id'

map⇑^-id : ∀ n {α} {f : α → α} (pf : f ~ id) → map⇑^ n f ~ id
map⇑^-id zero    = id
map⇑^-id (suc n) = map⇑-id ∘ map⇑^-id n

module _ {α β γ}{f : β → γ}{g : α → β}{h : α → γ}(h= : f ∘ g ~ h) where
    map▹-∘ : ∀ b0 b1 b2 → map▹ b1 b2 f ∘ map▹ b0 b1 g ~ map▹ b0 b2 h
    map▹-∘ b0 b1 b2 (old x)   = ap old (h= x)
    map▹-∘ b0 b1 b2 (new .b0) = refl

    map⇑-∘ : map⇑ f ∘ map⇑ g ~ map⇑ h
    map⇑-∘ = map▹-∘ _ _ _

map⇑^-∘ : ∀ n {α β γ}{f : β → γ}{g : α → β}{h : α → γ}(h= : f ∘ g ~ h) → map⇑^ n f ∘ map⇑^ n g ~ map⇑^ n h
map⇑^-∘ zero    = id
map⇑^-∘ (suc n) = map⇑-∘ ∘ map⇑^-∘ n

module _ {α β γ}{f : β → γ}{g : α → β} where
    map▹-∘' : ∀ b0 b1 b2 → map▹ b1 b2 f ∘ map▹ b0 b1 g ~ map▹ b0 b2 (f ∘ g)
    map▹-∘' = map▹-∘ λ _ → refl

    map⇑-∘' : map⇑ f ∘ map⇑ g ~ map⇑ (f ∘ g)
    map⇑-∘' = map▹-∘' _ _ _

    map⇑^-∘' : ∀ n → map⇑^ n f ∘ map⇑^ n g ~ map⇑^ n (f ∘ g)
    map⇑^-∘' n = map⇑^-∘ n λ _ → refl

map⇑= : ∀ {α β} {f f' : α → β} (f= : f ~ f') → map⇑ f ~ map⇑ f'
map⇑= f= (old x)  = ap old (f= x)
map⇑= f= (new .♦) = refl

map⇑^= : ∀ n {α β} {f f' : α → β} (f= : f ~ f') → map⇑^ n f ~ map⇑^ n f'
map⇑^= zero    = id
map⇑^= (suc n) = map⇑= ∘ map⇑^= n

mkScope : ∀ {w} (T : World -> Set) -> Binder w -> Set
mkScope {w} T = λ b → T (w ▹ b)

ScopeP : (T : World → Set) → World → Set
ScopeP = λ T w → NablaP w (mkScope T)

ScopeS : (T : World → Set) → World → Set
ScopeS = λ T w → NablaS w (mkScope T)

ScopeF : (T : World → Set) → World → Set
ScopeF = λ T w → NablaF w (mkScope T)

-- ScopeFFunctor : ∀ {F} -> Functor F -> Functor (ScopeF F)
-- ScopeFFunctor F = record { _<$>_ = λ f s →  map⇑ f <$> s
--                          ; <$>-id = λ pf → <$>-id (map▹-id pf)
--                          ; <$>-∘ = λ h= → <$>-∘ (map⇑-∘ h=) }

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

instance
  ⇉-skip :  ∀ {α β : World} {b} → {{s : Box (α → β)}} → Box (α → β ▹ b)
  ⇉-skip {{box s}} = box (old ∘ s)

  ⇉-refl : ∀ {w : World} → Box (w → w)
  ⇉-refl = box id

⇉^ : ∀ n {α} → Box (α → α ⇑^ n)
⇉^ n = box (old^ n)

  -- ⇉-▹ :  ∀ {α β}{{s : α ⇉ β}} → (α ▹ ♦) ⇉ (β ▹ ♦)
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x -> map▹ ♦ ♦ s x

  -- ⇉-▹ :  ∀ {α β}{b}{b'}{{s : α ⇉ β}} → (α ▹ b) ⇉ (β ▹ b')
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ _ s x

  {- not sure on how instance arguments

  ⇉-▹ :  ∀ {α β}{b}{{s : α ⇉ β}}{{b'}} → (α ▹ b) ⇉ (β ▹ b')
  ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ s x
  -}
record Functor (F : Set -> Set) : Set1 where
  -- Kleisli arrow (useful at this level even though we do not have a category yet.)
  infixr 0 _→K_
  _→K_ : Set -> Set -> Set
  _→K_ A B = A → F B
  infixl 4 _<$>_
  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B

  map : ∀ {A B} → (A → B) → F A → F B
  map = _<$>_
  field
    <$>-id : ∀ {α}{f : α → α} (pf : f ~ id) → _<$>_ f ~ id
    <$>-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ}
            (h= : f ∘ g ~ h)
          → map f ∘ map g ~ map h

  <$>-id' : ∀ {α} → _<$>_ {α} id ~ id
  <$>-id' = <$>-id (λ _ → refl)

  <$>-∘' : ∀ {α β γ}{f : β → γ}{g : α → β}
          → map f ∘ map g ~ map (f ∘ g)
  <$>-∘' = <$>-∘ (λ _ → refl)

module Renaming {F} (Fun-F : Functor F) where
  open Functor Fun-F

  ----------------------------
  -- Weakening/Renaming
  wkN' : ∀ {α β : World} {{s : Box (α → β)}} → α → β
  wkN' = unbox …

  _∈_ : ∀ {w}(b : Binder w)(w' : World) → Set
  b ∈ w' = Box ((_ ▹ b) → w')

  name' : ∀ {w w'}(b : Binder w) {{s : b ∈ w'}} → w'
  name' b = wkN' (name b)

  wk : ∀ {α β} {{s : Box (α → β)}} → F α → F β
  wk  = map wkN'

  wk^ : ∀ n {α} → F α → F (α ⇑^ n)
  wk^ n = wk {{⇉^ n}}

  atVar' : {α β : World} -> ScopeF F α -> (b : Binder β) → {{_ : Box (α → β)}} -> F (β ▹ b)
  atVar'  sc b {{box s}} = map▹ _ _ s <$> sc

functorId :  Functor (\x -> x)
functorId = record { _<$>_ = id ; <$>-id = λ pf x → pf x ; <$>-∘ = λ h= x → h= x }

record PointedFunctor (F : Set -> Set) : Set1 where
  constructor mk
  field
    {{isFunctor}} : Functor F
    return : ∀ {A} → A → F A

  open Functor isFunctor

  field
    map-return' : ∀ {a b} (f : a -> b) -> ∀ x -> f <$> return x == return (f x)

  map-return : ∀ {a b} (f : a -> b) {s : a →K a} (s= : s ~ return) -> ∀ x -> f <$> s x == return (f x)
  map-return f {s} s= x with s x | s= x
  ... | ._ | refl = map-return' f x

module PointedRenaming {F} (Fun-F : PointedFunctor F) where
  open PointedFunctor Fun-F
  open Functor isFunctor
  open Renaming isFunctor public

  var' : ∀ {w w'}(b : Binder w){{s : Box ((w ▹ b) → w')}} → F w'
  var' b = return (name' b)

  -- Same as ext but with abstract b b'
  ext▹ : ∀ {α β} b b' → α →K β → (α ▹ b) →K (β ▹ b')
  ext▹ _ _ θ (old x)  = wk (θ x)
  ext▹ b _ θ (new .b) = return (new _)

  liftSubst = ext▹

  ext : ∀ {v w} (s : v →K w) → v ⇑ →K w ⇑
  ext = ext▹ _ _

  ext^ : ∀ n {v w} (s : v →K w) → v ⇑^ n →K w ⇑^ n
  ext^ zero    = id
  ext^ (suc n) = ext ∘ ext^ n

  ext-return : ∀ {α}  {s : α →K α} (s= : s ~ return)  → ext s ~ return
  ext-return s= (old x)  = map-return old s= x
  ext-return s= (new ._) = refl

  ext-return^ : ∀ n {α}  {s : α →K α} (s= : s ~ return)  → ext^ n s ~ return
  ext-return^ zero    = id
  ext-return^ (suc n) = ext-return ∘ ext-return^ n

  ext-return^' : ∀ n {α} → ext^ n {α} return ~ return
  ext-return^' n = ext-return^ n λ _ → refl

  ext-map▹ : ∀ {α β γ} b b' b'' {f : β → F γ} {g : α → β} {h : α → F γ}(h= : f ∘ g ~ h)
            → ext▹ b' b'' f ∘ map▹ b b' g ~ ext▹ b b'' h
  ext-map▹ _ _ _ h= (old _)  = ap (map old) (h= _)
  ext-map▹ _ _ _ h= (new ._) = refl

  ext-map⇑ : ∀ {α β γ}{f : β → F γ} {g : α → β} {h : α → F γ}(h= : f ∘ g ~ h)
            → ext f ∘ map⇑ g ~ ext h
  ext-map⇑ = ext-map▹ _ _ _

  ext-map⇑' : ∀ {α β γ}{f : β → F γ}{g : α → β} → ext f ∘ map⇑ g ~ ext (f ∘ g)
  ext-map⇑' = ext-map⇑ λ _ → refl

  ext-map⇑^ : ∀ n {α β γ}{f : β → F γ}{g : α → β}{h : α → F γ}(h= : f ∘ g ~ h) → ext^ n f ∘ map⇑^ n g ~ ext^ n h
  ext-map⇑^ zero    = id
  ext-map⇑^ (suc n) = ext-map⇑ ∘ ext-map⇑^ n

  ext-map⇑^' : ∀ n {α β γ}{f : β → F γ}{g : α → β} → ext^ n f ∘ map⇑^ n g ~ ext^ n (f ∘ g)
  ext-map⇑^' n = ext-map⇑^ n λ _ → refl

  module _ {α β γ δ}
           {f  : α → γ}
           {s  : γ →K δ}
           {f' : β → δ}
           {s' : α →K β}
           (s= : s ∘ f ~ map f' ∘ s') where
    -- TODO could take advantage of ext-map⇑
    ext-wk-subst : ext s ∘ map⇑ f ~ map (map⇑ f') ∘ ext s'
    ext-wk-subst (old x) = ap wk (s= x) ∙ <$>-∘' (s' x) ∙ ! <$>-∘' (s' x)
    ext-wk-subst (new ._) = ! map-return (map⇑ f') (λ x → refl) (new ◆)

  ext-ren-subst : ∀ {α β} {f : α → β}{s : α →K β} (s= : (return ∘ f) ~ s) → (return ∘ map⇑ f) ~ ext s
  ext-ren-subst {s = s} s= (old x) with s x | s= x
  ext-ren-subst {f = f} s= (old x) | ._ | refl = ! map-return old (\x -> refl) (f x)
  ext-ren-subst s= (new ._) = refl

  infix 3 _≔_
  infix 10 0≔_

  _≔_ : ∀ {α} b → F α → (α ▹ b) →K α
  (b ≔ u) (old x)  = return x
  (b ≔ u) (new .b) = u

  0≔_ : ∀ {α} → F α → (α ⇑) →K α
  0≔ u = ♦ ≔ u

  ≔-map : ∀ {α β} b b' (f : α → β) (t : F α) → (b' ≔ f <$> t) ∘ map▹ b b' f ~ map f ∘ (b ≔ t)
  ≔-map b b' f t (old x)  = ! map-return' f x
  ≔-map b b' f t (new ._) = refl

  0≔-map : ∀ {α β} (f : α → β) (t : F α) → 0≔(f <$> t) ∘ map⇑ f ~ map f ∘ 0≔ t
  0≔-map = ≔-map ♦ ♦

  ext-map⇑-old-return^ : ∀ n {α} b (t : F α) → ext^ n (b ≔ t) ∘ map⇑^ n old ~ return
  ext-map⇑-old-return^ n b t u = ext-map⇑^' n u ∙ ext-return^' n u

pointedId : PointedFunctor id
pointedId = mk {{functorId}} id (λ f x → refl)

record Applicative (F : Set -> Set) : Set1 where
  field
    _<*>_ : ∀ {A B} → F (A -> B) → F A -> F B

applicId :  Applicative (\x -> x)
applicId = record { _<*>_ = id }

record Monad (M : Set -> Set) : Set1 where
  infixl 5 _>>=_
  infixr 5 _=<<_
  field
    {{isPointed}} : PointedFunctor M
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

  open PointedFunctor isPointed
  open Functor isFunctor

  _=<<_ : ∀ {A B} → (A → M B) → M A  → M B
  _=<<_ = λ f m → m >>= f

  -- Too many names for the same thing...
  subs = _=<<_

  join : ∀ {A} -> M (M A) -> M A
  join x = x >>= id

  -- Kleisli composition
  _∘k_ : ∀ {α β γ} (s : β →K γ) (s' : α →K β) → α →K γ
  _∘k_ s s' = subs s ∘ s'

  field
    bind-assoc : ∀ {α β γ} {s : β →K γ} {s' : α →K β} {s'' : α →K γ} (s= : (s ∘k s') ~ s'') → subs s ∘ subs s' ~ subs s''
    right-id : ∀ {α}{s} (s= : s ~ return) → subs {α} s ~ id
    left-id : ∀ {α β x} {f : α →K β}{s} (s= : s ~ return)  -> s x >>= f == f x
    map-bind : ∀ {α β} {f : α → β} {s : α →K β} (s= : return ∘ f ~ s) → map f ~ subs s
                 --f <$> t == t >>= (\x -> return (f x))

  bind-assoc' : ∀ {α β γ} {s : β →K γ} {s' : α →K β} → subs s ∘ subs s' ~ subs (s ∘k s')
  bind-assoc' = bind-assoc λ _ → refl

  right-id' : ∀ {α} → subs {α} return ~ id
  right-id' = right-id λ _ → refl

  map-bind'  : ∀ {α β} {f : α → β} -> map f ~ subs (return ∘ f)
  map-bind' = map-bind λ _ → refl

  left-id' : ∀ {α β x} {f : α →K β} -> return x >>= f == f x
  left-id' = left-id λ _ → refl

  -- associativity, but with one substitution specialised to map
  bind∘map : ∀ {a b c} (t : M a) (f : a -> b) (s : b -> M c) -> ((f <$> t) >>= s) == (t >>= (s ∘ f))
  bind∘map t f s = ap (subs s) (map-bind' t) ∙ bind-assoc (λ _ → left-id') t

  -- another name for bind∘map
  =<<-<$> : ∀ {α β γ} {f : β →K γ} {g : α → β} t → f =<< (g <$> t) == f ∘ g =<< t
  =<<-<$> t = bind∘map t _ _

  <$>-=<< : ∀ {{_ : FunExt}} {α β γ} {f : β → γ} {g : α →K β} t → f <$> (g =<< t) == map f ∘ g =<< t
  <$>-=<< {f = f} {g} t = map-bind' (g =<< t) ∙ bind-assoc' t ∙ ap (_>>=_ t) (λ= (!_ ∘ map-bind' ∘ g))

module Substitution {M} (Mon-M : Monad M) where
  open Monad Mon-M
  open PointedFunctor isPointed
  open Functor isFunctor
  open PointedRenaming isPointed public

  -- Too many names for the same thing...
  [_]_ = subs

  substituteOut : ∀  {a} b ->  M a -> M (a ▹ b) -> M a
  substituteOut b u t = [ b ≔ u ] t

  -- (>>=) f == join ∘ fmap f
  -- subs-join∘ren : ∀ {α β} {f : Set -> Set} {{_ : Monad f}} (s : α →K β) → subs s ~ join ∘ _<$>_ s
  -- subs-join∘ren {{Mon}} s t = {!!}

  -- map (map⇑^ n old) is a form of weakening
  subst-ext^-subst0-wk^-id : ∀ n {a b} {t : M (a ⇑^ n)}{u}
    → subs (ext^ n (b ≔ u)) (map (map⇑^ n old) t) == t
  subst-ext^-subst0-wk^-id n {t = t} {u} = =<<-<$> t ∙ right-id (ext-map⇑-old-return^ n _ u) t

  subst0-ext : ∀ {α β} {s : α → M β} {u} → subs (0≔ (subs s u)) ∘ ext s ~ subs s ∘ 0≔ u
  subst0-ext (old x)  = subst-ext^-subst0-wk^-id 0 ∙ ! left-id'
  subst0-ext (new .♦) = left-id'

  {-
  We can define ANOTHER functor instance, but this is not really good.
  instance
    functor : Functor M
    functor = record { _<$>_ = λ f m → m >>= (λ x → return (f x))
                     ; <$>-id = λ pf → right-id (λ x₁ → ap return (pf x₁))
                     ; <$>-∘ = λ h= → bind-assoc (λ x₁ → trans left-id (ap return (h= x₁))) }
  -- open Functor functor public
  -}

module Auto where
    open Monad          {{...}} public
    open PointedFunctor {{...}} public
    open Applicative    {{...}} public
    open Functor        {{...}} public

module Term-Structure {F} (M : Monad F) where
    open Monad          M         public
    open PointedFunctor isPointed public
    -- open Applicative    {{...}} public
    open Functor        isFunctor public
    open Substitution   M         public

{-
module Auto {F : Set -> Set} where
    module _ {{F : Monad F}} where
      open Monad F public
    module _ {{F : PointedFunctor F}} where
      open PointedFunctor F public
    module _ {{F : Applicative F}} where
      open Applicative F public
    module _ {{F : Functor F}} where
      open Functor F public
-}



-- Note that one cannot define lambda in terms of >>=:
-- lambda : ∀ {m a} -> {{_ : Monad m}} -> m (a ▹ ◆) -> m a
-- lambda t = t >>= (λ {(old x) → return x ; (new ._) → {!!} })


{-
module Free where
  open Auto
  -- Maybe we can make a version of "free" which supports lambdas.

  -- This should probably be defined using copatterns/whatnot, without nonsense.
  data Free (f : Set -> Set) (a : Set) : Set where
    pure : a -> Free f a
    embed : f (Free f a) -> Free f a

  {-# NO_TERMINATION_CHECK #-}
  Free-fmap : ∀ {f a b} {{Fun : Functor f}} -> (a -> b) -> Free f a -> Free f b
  Free-fmap f (pure x) = pure (f x)
  Free-fmap f (embed m) = embed (Free-fmap f <$> m )

  {-# NO_TERMINATION_CHECK #-}
  Free-bind : ∀ {f a b} {{Fun : Functor f}} -> Free f a -> (a -> Free f b) -> Free f b
  Free-bind (pure x) f = f x
  Free-bind (embed m) f = embed ((λ x → Free-bind x f) <$> m)
  
  instance
    Free-Fun : ∀ {f} -> {{_ : Functor f}} -> Functor (Free f)
    Free-Fun = record { _<$>_ = Free-fmap ; <$>-id = {!!} ; <$>-∘ = {!!} }

    Free-Mon : ∀ {f} -> {{Fun : Functor f}} -> Monad (Free f)
    Free-Mon {f} {{Fun}} = record
                             { return = pure
                             ; _>>=_ = Free-bind
                             ; bind-assoc = {!!}
                             ; right-id = {!!}
                             ; left-id = {!!}
                             ; fmap-bind = {!!}
                             }
   
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

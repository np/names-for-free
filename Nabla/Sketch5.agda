open import Function.Extensionality
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Binary.PropositionalEquality.NP renaming (_≡_ to _==_; _≗_ to _~_)
open import Function

ap2 : ∀ {a b c : Set} {x1 x2 : a} {y1 y2 : b} -> (f : a -> b -> c) -> (x1 == x2) -> (y1 == y2) -> f x1 y1 == f x2 y2
ap2 f refl refl = refl

Type = Set
Type1 = Set1

Grph : ∀ {A B : Type} (f : A → B) → A → B → Type
Grph f x y = f x == y

_⇒_ : ∀ {A B : Type} (R S : A → B → Type) → Type
R ⇒ S = ∀ {x y} → R x y → S x y

… : ∀ {a} {A : Set a} {{x : A}} → A
… {{x}} = x

data Zero : Type where

data Bool : Type where
  true false : Bool

record One : Type where
  constructor tt

T : Bool -> Type
T true = One
T false = Zero

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

World = Type -- a context of names

-- type of a binder fresh for w. ('b:Binder w' could be written 'b∉w')
data Binder (w : World) : Set where
  ♦ : Binder w
-- postulate
--   Binder : (w : World) → Set
--   ♦ : ∀ {w} → Binder w

fresh : ∀ w -> Binder w
fresh _ = ♦

data Var (w : World) (b : Binder w) : Type where
  old : w → Var w b
  new : Var w b

infixr 5 _▹_
_▹_ : (w : World) (b : Binder w) → World
_▹_ = Var

-- World extended with a fresh variable.
_⇑ : (w : World) → World
w ⇑ = w ▹ ♦

-- b # v and b' # w
map▹  : ∀ {v w b} b' -> (v → w) → (v ▹ b) → (w ▹ b')
map▹ _ f (old x) = old (f x)
map▹ _ f new = new

map▹-id : ∀ {α}{f : α → α} (pf : f ~ id){b'} → map▹ b' f ~ id
map▹-id pf (old x) = ap old (pf x)
map▹-id pf new = refl

map▹-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ} b0 b1 b2 (h= : f ∘ g ~ h)
        → map▹ b2 f ∘ map▹ {b = b0} b1 g ~ map▹ b2 h
map▹-∘ b0 b1 b2 h= (old x) = ap old (h= x)
map▹-∘ b0 b1 b2 h= new = refl

-- Map to a fresh thing
map⇑  : ∀ {v w} -> (v → w) → (v ⇑) → (w ⇑)
map⇑ = map▹ ♦

NablaP : ∀ w → (T : Binder w → Set) → Set
NablaP = λ w T → Π (Binder w) T

NablaS : ∀ w → (T : Binder w → Set) → Set
NablaS = λ w T → Σ (Binder w) T

NablaF : ∀ w → (T : Binder w → Set) → Set
NablaF = λ w T → T ♦

ScopeP : (T : World → Set) → World → Set
ScopeP = λ T w → NablaP w (λ b → T (w ▹ b))

ScopeS : (T : World → Set) → World → Set
ScopeS = λ T w → NablaS w (λ b → T (w ▹ b))

ScopeF : (T : World → Set) → World → Set
ScopeF = λ T w → NablaF w (λ b → T (w ▹ b))

-- Scopes -- Representations of ∇(b∉w). T[b]
pack   : {w : World} (T : Binder w → Set) → NablaP w T → NablaS w T
pack {w} T f = ♦ , f ♦

unpack : {w : World} (T : Binder w → Set) → NablaS w T → NablaP w T
unpack T (♦ , t) ♦ = t

FS : {w : World} (T : Binder w → Set) → NablaF w T → NablaS w T
FS T x = ♦ , x

SF : {w : World} (T : Binder w → Set) → NablaS w T → NablaF w T
SF T (♦ , t) = t

FP : {w : World} (T : Binder w → Set) → NablaF w T → NablaP w T
FP T x = λ {♦ → x}

PF : {w : World} (T : Binder w → Set) → NablaP w T → NablaF w T
PF T x = x ♦


{-
binder-uniq : ∀ {w} (b₀ b₁ : Binder w) → b₀ == b₁
binder-uniq ♦ ♦ = refl

nablaS= : {w : World} (T : Binder w → Set)
          {x y : NablaS w T} → tr T (binder-uniq _ _) (snd x) == snd y → x == y
nablaS= T = pair= (binder-uniq _ _) 

packScope : {w : World} (T : World → Set) → ScopeP T w → ScopeS T w
packScope {w} T = pack λ b → T (w ▹ b)
unpackScope : {w : World} (T : World → Set) → ScopeS T w → ScopeP T w
unpackScope {w} T = unpack λ b → T (w ▹ b)
-}

{-
unpackPackScope : ∀ {w : World}  T (g : ScopeP T w) -> g == unpackScope T (packScope T g)
unpackPackScope T g = {!!} -- assumption

sndPack' : ∀ {w : World}  T (g : ScopeP T w) ->
           g _  ==  snd (packScope T g)
sndPack' T g = {!!}  -- unpackPackScope + injective pairs

sndPack : ∀ {w : World}  T (g : ScopeP T w) -> (P : T (w ▹ _) -> Set) ->
           P (g _)  -> P  (snd (packScope T g))
sndPack T g P p = {!subst sndPack'!} 
-}
    -- Alternative is to use an abstract scope (Nabla) as actual representation; possibly more accurate than both the above.
      -- Nabla : ∀ w → (T : Binder w → Set) → Set
      -- toPi   : ∀ {w T} -> Nabla w T -> Π(Binder w) T
      -- fromPi : ∀ {w T} -> Π(Binder w) T -> Nabla w T 
      -- etc.


    -- no  need for the empty world; we can quantify on all worlds.

-- refer a specific binder
name : ∀ {w} → (b : Binder w) → w ▹ b
name b = new

exportN : ∀ {α b} → (n : α ▹ b) → (name b == n) ⊎ α
exportN (old x) = right x
exportN new = left refl

exportN-name : ∀ {α} (b : Binder α) → exportN (name b) == left refl
exportN-name b = refl

record _⇉_ (α β : World) : Set where
  constructor mk⇉
  field
    wkN : α → β
open _⇉_ public

instance
  ⇉-skip :  ∀ {α} {b} → α ⇉ ( α ▹ b )
  ⇉-skip = mk⇉ old

  ⇉-refl : ∀ {w} → w ⇉ w
  ⇉-refl = mk⇉ λ x → x

  -- ⇉-▹ :  ∀ {α β}{{s : α ⇉ β}} → (α ▹ ♦) ⇉ (β ▹ ♦)
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ ♦ s x

  ⇉-▹ :  ∀ {α β}{b}{b'}{{s : α ⇉ β}} → (α ▹ b) ⇉ (β ▹ b')
  ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ _ s x

  {- not sure on how instance arguments

  ⇉-▹ :  ∀ {α β}{b}{{s : α ⇉ β}}{{b'}} → (α ▹ b) ⇉ (β ▹ b')
  ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ s x
  -}

wkN' : ∀ {α β} {{s : α ⇉ β}} → α → β
wkN' = wkN …

name' : ∀ {w w'}(b : Binder w) {{s : (w ▹ b) ⇉ w'}} → w'
name' b = wkN' (name b)

module Example-TmFresh where

  data Tm (w : World) : Type where
    var : w -> Tm w
    lam : ScopeF Tm w -> Tm w
    app : Tm w -> Tm w -> Tm w

  lamP : ∀ {w} → ScopeP Tm w -> Tm w
  lamP f = lam (f ♦)
 
  var' : ∀ {w w'}(b : Binder w){{s : (w ▹ b) ⇉ w'}} → Tm w'
  var' b = var (name' b)

  idTm : ∀ {w} -> Tm w
  idTm = lamP λ x → var (name x)
  
  apTm : ∀ {w} (b : Binder w) -> Tm w
  apTm {w} b = lamP λ x → lamP λ y → lamP λ z → app {!var' x!} (var' y)

  ap' : ∀ {w} -> ScopeP (ScopeP Tm) w
  ap' = λ x → λ y → app (var' x) (var' y)

  -- invalid!
  -- invalid : ∀ {w} (b : Binder w) → Tm ((w ▹ b) ▹ b)
  -- invalid = λ b → ap' b b

  module Trv
    {_⇶_ : World → World → Type}.b
    (vr  : ∀ {α β} → α ⇶ β → α → Tm β)
    (ext : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑) where

    trvT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
    trvT s (var x) = vr s x
    trvT s (lam t) = lam (trvT (ext s) t)
    trvT s (app t u) = app (trvT s t) (trvT s u)

  -- open Trv (λ f x → var (f x)) map⇑ public renaming (trvT to renT)

  renT : ∀ {α β} → (α → β) → Tm α → Tm β
  renT f (var x)       = var (f x)
  renT f (lam t)       = lam (renT (map▹ ♦ f) t)
  renT f (app t u)     = app (renT f t) (renT f u)

  renT-id : ∀ {α}{f : α → α} (pf : f ~ id) → renT f ~ id
  renT-id f (var x) = ap var (f x)
  renT-id f (lam t) = ap lam (renT-id (map▹-id f) t)
  renT-id f (app t t₁) = ap₂ app (renT-id f t) (renT-id f t₁)

  renT-id′ : ∀ {α} → renT {α} id ~ id
  renT-id′ = renT-id {f = λ x → x} (λ _ → refl)

  renT-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ}
            (h= : f ∘ g ~ h)
          → renT f ∘ renT g ~ renT h
  renT-∘ h= (var x) = ap var (h= x)
  renT-∘ h= (lam t) = ap lam (renT-∘ (map▹-∘ _ _ _ h=) t)
  renT-∘ h= (app t u) = ap2 app (renT-∘ h= t) (renT-∘ h= u)

  renT-∘′ : ∀ {α β γ}{f : β → γ}{g : α → β}
           → renT f ∘ renT g ~ renT (f ∘ g)
  renT-∘′ = renT-∘ (λ x → refl)

  _⇶_ : World → World → Type
  α ⇶ β = α → Tm β

  -- return . f ≡ fmap f . return
  renT∘var : ∀ {α β} (f : α → β) → var ∘ f ~ renT f ∘ var
  renT∘var f x = refl

  wkT : ∀ {α β} {{s : α ⇉ β}} → Tm α → Tm β
  wkT = renT wkN'
  -- wkT : ∀ {α b} → Tm α → Tm (α ▹ b)
  -- wkT = renT old
  -- wkT : ∀ {α β} {{i : α ⊆ β}} → Tm α → Tm β
  -- wkT = renT (wk …)

  wkT' : ∀ {α β} (s : α ⇉ β) → Tm α → Tm β
  wkT' (mk⇉ wk) = renT wk

  η : ∀ {w} → Tm w → Tm w
  η t = lamP λ x → app (wkT t) (var' x)

  ext : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑
  ext f (old x) = wkT (f x)
  ext f new     = var new

  -- open Trv (λ f → f) ext public renaming (trvT to substT)
  
  substT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
  substT s (var x) = s x
  substT s (lam t) = lam (substT (ext s) t)
  substT s (app t u) = app (substT s t) (substT s u)

  joinT : ∀ {α} → Tm (Tm α) → Tm α
  joinT = substT id

  -- (return x) >>= f   ≡   f x
  -- by definition

  _∘s_ : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) → α ⇶ γ
  (s ∘s s') x = substT s (s' x)

  ext-var : ∀ {α}{s : α ⇶ α} (s= : s ~ var) → ext s ~ var
  ext-var s= (old x) = ap wkT (s= x)
  ext-var s= new     = refl

  -- m >>= return   ≡   m
  subst-var : ∀ {α}{s} (s= : s ~ var) → substT {α} s ~ id
  subst-var s= (var x) = s= x
  subst-var s= (lam t) = ap lam (subst-var (ext-var s=) t)
  subst-var s= (app t u) = ap₂ app (subst-var s= t) (subst-var s= u)

  subst-var′ : ∀ {α} → substT {α} var ~ id
  subst-var′ = subst-var (λ _ → refl)

  ext-ren-subst : ∀ {α β} {f : α → β}{s : α ⇶ β} (s= : (var ∘ f) ~ s) → (var ∘ map▹ ♦ f) ~ ext s
  ext-ren-subst s= (old x) = ap wkT (s= x)
  ext-ren-subst s= new     = refl

  -- liftM == fmap
  -- NP: my hope with trvT was to avoid this proof...
  -- At least it could be generalized
  ren-subst : ∀ {α β} {f : α → β} {s : α ⇶ β}
                (s= : var ∘ f ~ s)
             → renT f ~ substT s
  ren-subst s= (var x) = s= x
  ren-subst s= (lam t) = ap lam (ren-subst (ext-ren-subst s=) t)
  ren-subst s= (app t u) = ap₂ app (ren-subst s= t) (ren-subst s= u)

  ren-subst′ : ∀ {α β} (f : α → β)
             → renT f ~ substT (var ∘ f)
  ren-subst′ f = ren-subst {f = f} λ x → refl

  subst-var∘old : ∀ {α b} → wkT ~ substT (var ∘ old {α} {b})
  subst-var∘old = ren-subst′ old

  module Alt-ext where
    ext' : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑
    ext' f (old x) = substT (var ∘ old) (f x)
    ext' f new     = var new

    ext-ext' : ∀ {α β} (s : α ⇶ β)
               → ext s ~ ext' s
    ext-ext' s (old x) = subst-var∘old (s x)
    ext-ext' s new = refl

  ext-wk-subst : ∀ {α β γ δ}
                   {f  : α → γ}
                   {s  : γ ⇶ δ}
                   {f' : β → δ}
                   {s' : α ⇶ β}
                   (q : s ∘ f ~ renT f' ∘ s')
                 → ext s ∘ map⇑ f ~ renT (map⇑ f') ∘ ext s'
  ext-wk-subst q (old x) = ap wkT (q x) ∙ renT-∘′ _ ∙ ! renT-∘′ _
  ext-wk-subst q new = refl

  subst∘ren : ∀ {α β γ δ}
               {f  : α → γ}
               {s  : γ ⇶ δ}
               {f' : β → δ}
               {s' : α ⇶ β}
               (q : s ∘ f ~ renT f' ∘ s')
              → substT s ∘ renT f ~ renT f' ∘ substT s'
  subst∘ren q (var x) = q x
  subst∘ren q (lam t) = ap lam (subst∘ren (ext-wk-subst q) t)
  subst∘ren q (app t u) = ap₂ app (subst∘ren q t) (subst∘ren q u)

  ext-hom : ∀ {α β γ}
              {s : β ⇶ γ} {s' : α ⇶ β} {s'' : α ⇶ γ}
              (s= : (s ∘s s') ~ s'')
            → (ext s ∘s ext s') ~ ext s''
  ext-hom {s = s} {s'} {s''} s= (old x) =
    subst∘ren (λ x → refl) (s' x)
    ∙ ap wkT (s= x)
  ext-hom s= new = refl

  -- (m >>= f) >>= g   ≡   m >>= ( \x -> (f x >>= g) )
  subst-hom : ∀ {α β γ}
                 {s : β ⇶ γ} {s' : α ⇶ β} {s'' : α ⇶ γ}
                 (s= : (s ∘s s') ~ s'')
               → substT s ∘ substT s' ~ substT s''
  subst-hom s= (var x) = s= x
  subst-hom s= (lam t) = ap lam (subst-hom (ext-hom s=) t)
  subst-hom s= (app t u) = ap₂ app (subst-hom s= t) (subst-hom s= u)

  subst-hom′ : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β)
               → substT s ∘ substT s' ~ substT (s ∘s s')
  subst-hom′ s s' t = subst-hom (λ _ → refl) t

  -- (>>=) f == join ∘ fmap f
  subst-join∘ren : ∀ {α β} (s : α ⇶ β) → substT s ~ joinT ∘ renT s
  subst-join∘ren s t =
    !(subst∘ren {f = s}{id}{id}{s} (λ x → ! renT-id′ (s x)) t
      ∙ renT-id′ _)

  {-
These should be derivable from the previous lemmas only:

join . fmap join     ≡ join . join
  using subst-join∘ren and substsubst-var′

join . fmap return   ≡ join . return = id
  using subst-join∘ren and subst-var′

join . fmap (fmap f) ≡ fmap f . join
  -}

-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

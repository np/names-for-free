open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)
open import Function

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

  functor : Functor M
  functor = record { _<$>_ = λ f m → m >>= (λ x → return (f x))
                   ; <$>-id = λ pf → right-id (λ x₁ → ap return (pf x₁))
                   ; <$>-∘ = λ h= → bind-assoc (λ x₁ → trans left-id (ap return (h= x₁))) }
  open Functor functor public

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

data IVar {I : Type} {w : World} (Γ : w → I → Type)
          (b : Binder w) (i : I) : w ▹ b → I → Type where
  old : ∀ {j x} → Γ x j → IVar Γ b i (old x) j
  new : IVar Γ b i (new b) i

-- World extended with a fresh variable.
_⇑ : (w : World) → World
w ⇑ = w ▹ ♦

_,_↦_ : ∀ {I : Type}{w : World}
          (Γ : w → I → Type)(b : Binder w) → I → w ▹ b → I → Type
Γ , b ↦ i = IVar Γ b i

-- World extended with a fresh variable.
_,,_ : ∀ {I : Type}{w : World}(Γ : w → I → Type) → I → w ⇑ → I → Type
Γ ,, i = Γ , ♦ ↦ i

-- b # v and b' # w
map▹  : ∀ {v w b} b' -> (v → w) → (v ▹ b) → (w ▹ b')
map▹ _ f (old x) = old (f x)
map▹ _ f (new _) = new _

map▹-id : ∀ {α}{f : α → α} (pf : f ~ id){b'} → map▹ b' f ~ id
map▹-id pf (old x) = ap old (pf x)
map▹-id pf (new _) = refl

map▹-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ} b0 b1 b2 (h= : f ∘ g ~ h)
        → map▹ b2 f ∘ map▹ {b = b0} b1 g ~ map▹ b2 h
map▹-∘ b0 b1 b2 h= (old x) = ap old (h= x)
map▹-∘ b0 b1 b2 h= (new .b0) = refl

-- Map to a fresh thing
map⇑  : ∀ {v w} -> (v → w) → (v ⇑) → (w ⇑)
map⇑ = map▹ ♦


ScopeP : (T : World → Set) → World → Set
ScopeP = λ T w → NablaP w (λ b → T (w ▹ b))

ScopeS : (T : World → Set) → World → Set
ScopeS = λ T w → NablaS w (λ b → T (w ▹ b))

ScopeF : (T : World → Set) → World → Set
ScopeF = λ T w → NablaF w (λ b → T (w ▹ b))


{-
nablaS= : {w : World} (T : Binder w → Set)
          {x y : NablaS w T} → tr T (binder-uniq _ _) (snd x) == snd y → x == y
nablaS= T = pair= (binder-uniq _ _) 

-}

pack : {w : World} (T : World → Set) → ScopeP T w → ScopeF T w
pack {w} T x = x ♦

unpack : {r : Set} {w : World} (T : World → Set) → ScopeF T w → (∀ v -> T (w ▹ v) -> r) -> r
unpack = λ {r} {w} T₁ z z₁ → z₁ ♦ z

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

instance
  ⇉-skip :  ∀ {α β} {b} → {{s : α ⇉ β}} → α ⇉ ( β ▹ b )
  ⇉-skip {{mk⇉ s}} = mk⇉ (λ x → old (s x))

  ⇉-refl : ∀ {w} → w ⇉ w
  ⇉-refl = mk⇉ λ x → x

  -- ⇉-▹ :  ∀ {α β}{{s : α ⇉ β}} → (α ▹ ♦) ⇉ (β ▹ ♦)
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ ♦ s x

  -- ⇉-▹ :  ∀ {α β}{b}{b'}{{s : α ⇉ β}} → (α ▹ b) ⇉ (β ▹ b')
  -- ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ _ s x

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
    -- lam : ScopeF Tm w -> Tm w
    lam : Tm (w ▹ ♦) → Tm w 
    app : Tm w -> Tm w -> Tm w

  lamP : ∀ {w} → ScopeP Tm w -> Tm w
  lamP f = lam (f ♦)
 
  var' : ∀ {w w'}(b : Binder w){{s : (w ▹ b) ⇉ w'}} → Tm w'
  var' b = var (name' b)

  idTm : ∀ {w} -> Tm w
  idTm = lamP λ x → var' x
  
  apTm : ∀ {w} (b : Binder w) -> Tm w
  apTm {w} b = lamP λ x → lamP λ y → lamP λ z → app (var' x) (var' y)

  ap' : ∀ {w} -> ScopeP (ScopeP Tm) w
  ap' = λ x → λ y → app (var' x) (var' y)

  -- invalid!
  -- invalid : ∀ {w} (b : Binder w) → Tm ((w ▹ b) ▹ b)
  -- invalid = λ b → ap' b b

  module Trv
    {_⇶_ : World → World → Type}
    (vr  : ∀ {α β} → α ⇶ β → α → Tm β)
    (ext : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑) where

    trvT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
    trvT s (var x) = vr s x
    trvT s (lam t) = lam (trvT (ext s) t)
    trvT s (app t u) = app (trvT s t) (trvT s u)

    module _
      (ext-var : ∀ {α}{s : α ⇶ α} (s= : vr s ~ var) → vr (ext s) ~ var)
      where

        trvT-vr : ∀ {α}{f : α ⇶ α} → vr f ~ var → trvT f ~ id
        trvT-vr s (var x) = s x
        trvT-vr s (lam t) = ap lam (trvT-vr (ext-var s) t)
        trvT-vr s (app t u) = ap₂ app (trvT-vr s t) (trvT-vr s u)

  -- open Trv (λ f → var ∘ f) map⇑ public renaming (trvT to renT)

  renT : ∀ {α β} → (α → β) → Tm α → Tm β
  renT f (var x)       = var (f x)
  -- renT f (lam t)       = lam (renT (map▹ ♦ f) t) -- using fresh
  renT f (lam t)       = lamP λ x -> renT (map▹ x f) t
  -- Even better: unpack lam t properly.
  -- renT f (lam t0) = unpack Tm t0 λ x t -> lamP (λ x' → renT (map▹ x' f) t)
  -- Unfortunately this jams the termination-checker.
  -- renT f (lam t)       = lamP λ b → (renT (map▹ b f) t)
    -- Even better: unpack lam t properly.
    -- renT f (lam t)       = lam (renT (map⇑ f) t)
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
  renT-∘ h= (app t u) = ap₂ app (renT-∘ h= t) (renT-∘ h= u)

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
  ext f (new ._)     = var (new ♦)

  -- open Trv (λ f → f) ext public renaming (trvT to substT)
  
  substT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
  substT s (var x) = s x
  substT s (lam t) = lam (substT (ext s) t)
  substT s (app t u) = app (substT s t) (substT s u)

  [_]_ = substT

  joinT : ∀ {α} → Tm (Tm α) → Tm α
  joinT = substT id

  -- (return x) >>= f   ≡   f x
  -- by definition

  _∘s_ : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) → α ⇶ γ
  (s ∘s s') x = substT s (s' x)

  ext-var : ∀ {α}{s : α ⇶ α} (s= : s ~ var) → ext s ~ var
  ext-var s= (old x) = ap wkT (s= x)
  ext-var s= (new ._)     = refl

  -- m >>= return   ≡   m
  subst-var : ∀ {α}{s} (s= : s ~ var) → substT {α} s ~ id
  subst-var s= (var x) = s= x
  subst-var s= (lam t) = ap lam (subst-var (ext-var s=) t)
  subst-var s= (app t u) = ap₂ app (subst-var s= t) (subst-var s= u)

  subst-var′ : ∀ {α} → substT {α} var ~ id
  subst-var′ = subst-var (λ _ → refl)

  ext-ren-subst : ∀ {α β} {f : α → β}{s : α ⇶ β} (s= : (var ∘ f) ~ s) → (var ∘ map▹ ♦ f) ~ ext s
  ext-ren-subst s= (old x) = ap wkT (s= x)
  ext-ren-subst s= (new ._)     = refl

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

  subst-var∘old : ∀ {α b} → wkT {α} {α ▹ b} ~ substT (var ∘ old)
  subst-var∘old = ren-subst′ old

  module Alt-ext where
    ext' : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑
    ext' f (old x) = substT (var ∘ old) (f x)
    ext' f (new ._)     = var (new _)

    ext-ext' : ∀ {α β} (s : α ⇶ β)
               → ext s ~ ext' s
    ext-ext' s (old x) = subst-var∘old (s x)
    ext-ext' s (new ._) = refl

  ext-wk-subst : ∀ {α β γ δ}
                   {f  : α → γ}
                   {s  : γ ⇶ δ}
                   {f' : β → δ}
                   {s' : α ⇶ β}
                   (q : s ∘ f ~ renT f' ∘ s')
                 → ext s ∘ map⇑ f ~ renT (map⇑ f') ∘ ext s'
  ext-wk-subst q (old x) = ap wkT (q x) ∙ renT-∘′ _ ∙ ! renT-∘′ _
  ext-wk-subst q (new ._) = refl

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
  ext-hom s= (new ._) = refl

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
  Tm-Monad : Monad Tm
  Tm-Monad = record
               { return = var
               ; _>>=_ = λ x x₁ → substT x₁ x
               ; bind-assoc = subst-hom
               ; right-id = subst-var
               ; left-id = λ {α} {β} {x} {f} → refl
               }

  swpLams : ∀ {w} -> Tm w -> Tm w
  swpLams (lam t0) = unpack Tm t0 (λ {v (lam t1) → unpack Tm t1 (λ v₁ t → lamP (λ x → lamP (λ x₁ → {!t [x := v1, x1 := v]!})))
                                     ;v t' → {!!}})
  -- swpLams (lam (lam t0)) = {!!}
  swpLams x = x
  {-
These should be derivable from the previous lemmas only:

join . fmap join     ≡ join . join
  using subst-join∘ren and substsubst-var′

join . fmap return   ≡ join . return = id
  using subst-join∘ren and subst-var′

join . fmap (fmap f) ≡ fmap f . join
  -}

  -- Types for STLC
  data Ty : Type where
    _⟶_ : (S T : Ty) → Ty
    nat : Ty

  -- Contexts for STLC
  Cx : World → Type1
  Cx α = α → Ty → Type

  -- Typing derivations for STLC
  infix 0 _⊢_∶_
  data _⊢_∶_ {α} (Γ : Cx α) : Cx (Tm α) where
    var : ∀ {x S} → Γ x S → Γ ⊢ var x ∶ S
    lam : ∀ {t T S}
          (t⊢ : Γ ,, S ⊢ t ∶ T)
          -------------------
          → Γ ⊢ lam t ∶ S ⟶ T
    app : ∀ {t u T S}
          (t⊢ : Γ ⊢ t ∶ S ⟶ T)
          (u⊢ : Γ ⊢ u ∶ S)
          -------------------
          → Γ ⊢ app t u ∶ T

  -- Lifts a "renaming" to context membership proofs.
  Ren⊢ : ∀ {α β}(Γ : Cx α)(Δ : Cx β)(f : α → β) → Type
  Ren⊢ Γ Δ f = ∀ {T x} → Γ x T → Δ (f x) T

  -- These renamings are compatible with world extension.
  extRen⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{s : α → β}{b b' i}
         → Ren⊢ Γ Δ s → Ren⊢ (Γ , b ↦ i) (Δ , b' ↦ i) (map▹ b' s)
  extRen⊢ r (old x) = old (r x)
  extRen⊢ r new = new

  -- Renaming in a typing derivation.
  ren⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{f : α → β}{t T}
       → Ren⊢ Γ Δ f
       → Γ ⊢ t ∶ T → Δ ⊢ renT f t ∶ T
  ren⊢ r⊢ (var x) = var (r⊢ x)
  ren⊢ r⊢ (lam d) = lam (ren⊢ (extRen⊢ r⊢) d)
  ren⊢ r⊢ (app d d₁) = app (ren⊢ r⊢ d) (ren⊢ r⊢ d₁)

  -- Lifts a substitution on terms as a substitution on
  -- typing derivations. Context membership proofs are
  -- mapped to typing derivations.
  Subst⊢ : ∀ {α β}(Γ : Cx α)(Δ : Cx β)(s : α ⇶ β) → Type
  Subst⊢ Γ Δ s = ∀ {T x} → Γ x T → Δ ⊢ s x ∶ T

  -- These substitutions are compatible with world extension.
  -- Weakening a derivation is a particular case of renaming.
  extSubst⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{s : α ⇶ β}{i}
         → Subst⊢ Γ Δ s → Subst⊢ (Γ ,, i) (Δ ,, i) (ext s)
  extSubst⊢ r (old x₁) = ren⊢ old (r x₁)
  extSubst⊢ r new = var new

  -- Substituting in a typing derivation.
  subst⊢ : ∀ {α β}{Γ : Cx α}{Δ : Cx β}{s : α ⇶ β}{t T}
           → Subst⊢ Γ Δ s
           → Γ ⊢ t ∶ T → Δ ⊢ [ s ] t ∶ T
  subst⊢ r (var x) = r x
  subst⊢ r (lam d) = lam (subst⊢ (extSubst⊢ r) d)
  subst⊢ r (app d d₁) = app (subst⊢ r d) (subst⊢ r d₁)

  -- TODO generalize (⇶,Tm)
  subst0 : ∀ {α b} → Tm α → (α ▹ b) ⇶ α
  subst0 u (old x) = var x
  subst0 u (new ._)     = u

  subst⊢0 : ∀ {α}{u : Tm α}{Γ b T}
            → Γ ⊢ u ∶ T → Subst⊢ (Γ , b ↦ T) Γ (subst0 u)
  subst⊢0 u (old x) = var x
  subst⊢0 u new     = u

  [0≔_]_ : ∀ {α b} (u : Tm α) → Tm (α ▹ b) → Tm α
  [0≔ u ] t = [ subst0 u ] t

  pattern _·_ t u = app t u
  pattern ƛ t = lam t

  infix 0 _↝_
  data _↝_ {α} : (t u : Tm α) → Type where
    β     : ∀ {t u} → ƛ t · u ↝ [0≔ u ] t
    [_]·_ : ∀ {t t'}(r : t ↝ t') u → t · u ↝ t' · u
    _·[_] : ∀ {t t'} u (r : t ↝ t') → u · t ↝ u · t'
    ƛ[_]  : ∀ {t t'}(r : t ↝ t') → ƛ t ↝ ƛ t'

  -- Type preservation: reduction preserves typing
  ↝-pres-⊢ : ∀ {α Γ T} {t t' : Tm α} → t ↝ t' → Γ ⊢ t ∶ T → Γ ⊢ t' ∶ T
  ↝-pres-⊢ β (ƛ t₁ · t₂) = subst⊢ (subst⊢0 t₂) t₁
  ↝-pres-⊢ ([ r ]· u) (t₁ · t₂) = ↝-pres-⊢ r t₁ · t₂
  ↝-pres-⊢ (u ·[ r ]) (t₁ · t₂) = t₁ · ↝-pres-⊢ r t₂
  ↝-pres-⊢ ƛ[ r ] (ƛ t₁) = ƛ (↝-pres-⊢ r t₁)

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

module Terms where

open import Sketch5
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)
open import Function

infix 5 _$$_
data Tm (w : World) : Type where
  var  : w -> Tm w
  ƛ_   : ScopeF Tm w -> Tm w
  _$$_ : Tm w -> Tm w -> Tm w

pattern app t u = t $$ u
pattern lam t = ƛ_ t

lamP : ∀ {w} → ScopeP Tm w -> Tm w
lamP f = lam (f ♦)


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
renT f (lam t)       = lamP λ x -> renT (map▹ ♦ x f) t
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
renT-∘ h= (lam t) = ap lam (renT-∘ (map⇑-∘ h=) t)
renT-∘ h= (app t u) = ap₂ app (renT-∘ h= t) (renT-∘ h= u)

renT-∘′ : ∀ {α β γ}{f : β → γ}{g : α → β}
         → renT f ∘ renT g ~ renT (f ∘ g)
renT-∘′ = renT-∘ (λ x → refl)

_⇶_ : World → World → Type
α ⇶ β = α → Tm β


instance
  Tm-Functor : Functor Tm
  Tm-Functor = record { _<$>_ = renT ; <$>-id = renT-id ; <$>-∘ = renT-∘ }

instance
  Tm-Pointed : PointedFunctor Tm
  Tm-Pointed = record { return = var ; map-return' = λ f x → refl }

idTm : ∀ {w} -> Tm w
idTm = lamP λ x → var' x

apTm : ∀ {w} (b : Binder w) -> Tm w
apTm {w} b = lamP λ x → lamP λ y → lamP λ z → app (var' x) (var' y)

ap' : ∀ {w} -> ScopeP (ScopeP Tm) w
ap' = λ x → λ y → app (var' x) (var' y)
  
wkT : ∀ {α β} {{s : α ⇉ β}} → Tm α → Tm β
wkT = wk

wkT' : ∀ {α β} (s : α ⇉ β) → Tm α → Tm β
wkT' (mk⇉ wk) = map wk

η : ∀ {w} → Tm w → Tm w
η t = lamP λ x → app (wkT t) (var' x)


-- open Trv (λ f → f) ext public renaming (trvT to substT)

substT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
substT s (var x) = s x
substT s (lam t) = lam (substT (ext s) t)
substT s (app t u) = app (substT s t) (substT s u)

-- (return x) >>= f   ≡   f x
-- by definition

-- Kleisli composition
_∘s_ : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) → α ⇶ γ
s ∘s s' = substT s ∘ s'


-- m >>= return   ≡   m
subst-var : ∀ {α}{s} (s= : s ~ var) → substT {α} s ~ id
subst-var s= (var x) = s= x
subst-var s= (lam t) = ap lam (subst-var (ext-var s=) t)
subst-var s= (app t u) = ap₂ app (subst-var s= t) (subst-var s= u)

-- subst-var′ : ∀ {α} → substT {α} var ~ id
-- subst-var′ = subst-var (λ _ → refl)

-- ext-ren-subst : ∀ {α β} {f : α → β}{s : α ⇶ β} (s= : (var ∘ f) ~ s) → (var ∘ map⇑ f) ~ ext s
-- ext-ren-subst s= (old x) = ap wkT (s= x)
-- ext-ren-subst s= (new ._)     = refl

-- liftM == fmap
-- NP: my hope with trvT was to avoid this proof...
-- At least it could be generalized
ren-subst : ∀ {α β} {f : α → β} {s : α ⇶ β}
              (s= : var ∘ f ~ s)
           → renT f ~ substT s
ren-subst s= (var x) = s= x
ren-subst s= (lam t) = ap lam (ren-subst (ext-ren-subst s=) t)
ren-subst s= (app t u) = ap₂ app (ren-subst s= t) (ren-subst s= u)

module Gen-Monad-Trav where
   module T
      {f : Set -> Set} {{_ : Functor f}}{{_ : Applicative f}}
      {g : Set -> Set} {{_ : Functor g}}{{_ : PointedFunctor g}}
      (vr : ∀ {b} -> g b -> f (Tm b))
     where
     trv : ∀ {a b : Set} (s : a → g b) ->  Tm a -> f (Tm b)
     trv s (var x) = vr (s x)
     trv {a} {b} s (ƛ x) = ƛ_ <$> trv extL x
       where extL : a ▹ ♦ → g (b ▹ ◆)
             extL (old x₂) = old <$> s x₂ -- "bitraverse▹"
             extL (new .♦) = return (new ♦)
     trv s (t $$ u) = (_$$_ <$> trv s t ) <*> trv s t

   postulate Tm' : (x : Set) -> (x' : x -> Set) -> Tm x -> Set
   module T'
    {f : Set -> Set} {{_ : Functor f}}{{_ : Applicative f}}
    (f' : (x : Set) -> (x' : x -> Set) -> f x -> Set)
    {g : Set -> Set} {{_ : Functor g}}{{_ : PointedFunctor g}}
    (g' : (x : Set) -> (x' : x -> Set) -> g x -> Set)
    (vr : ∀ {b} -> g b -> f (Tm b))
    (vr' : ∀ {b} -> (b' : b -> Set) -> (y : g b) -> (g' b b' y) -> f' (Tm b) (Tm' b b') (vr y) )
    where
    postulate trv' : ∀ {a} (a' : a -> Set) -> 
                     ∀ {b} (b' : b -> Set) ->
                     ∀ {s : a -> g b} (s' : {x : a} -> a' x -> g' b b' (s x)) ->
                     ∀ {t} -> Tm' a a' t ->
                     f' (Tm b) (Tm' b b') (T.trv vr s t)
   
   thm : ∀ {α}{s} (s= : s ~ var) → substT {α} s ~ id
   thm s= = {!T'.trv' ? ? (λ x → var <$> x) !}

     
{-   module Tᵣ
      {f : Set -> Set} {{_ : Functor f}}{{_ : Applicative f}}
      {g : Set -> Set} {{_ : Functor g}}{{_ : PointedFunctor g}}
      (v1 : ∀ {b} -> g b -> f (Tm b))
      (v2 : ∀ {b} -> g b -> f (Tm b))
      (vᵣ : ∀ {b1 b2} -> (br : b1 -> b2) -> (x1 : g b1) -> (x2 : g b2) -> (h : f (Tm b1) -> f (Tm b2)) -> ? -> map {{?}} h v1 == v2)
     where
      postulate
        trvᵣ : ∀ {a1 a2} -> (ar : a1 -> a2) ->
               ∀ {b1 b2} -> (br : b1 -> b2) ->
               ∀ {s1 : a1 -> g b1} {s2 : a2 -> g b2} -> (∀ {x1 x2} -> ar x1 == x2 -> (h : g b1 -> g b2) -> ? ->  map {{?}} h (s1 x1) == s2 x2)  ->
               ∀ (h : f (Tm b1) -> f (Tm b2)) ->
               map {{?}} h (T.trv v1 s1) == T.trv v2 s2
-}             
     

   traverse : ∀ {f : Set -> Set} {{_ : Functor f}}{{_ : PointedFunctor f}}{{_ : Applicative f}} {a b : Set} (s : a → f b) -> Tm a -> f (Tm b)
   traverse = T.trv (λ x → var <$> x)

   monad-bind : ∀ {a b : Set}  (s : a → Tm b) ->  Tm a -> Tm b
   monad-bind = T.trv {{functorId}} {{applicId}} id

   fmap : ∀ {a b : Set} (s : a → b) -> Tm a -> Tm b
   fmap = traverse {\x -> x}  {{functorId}} {{pointedId}} {{applicId}}

module Alt-ext where
  ren-subst′ : ∀ {α β} (f : α → β) → renT f ~ substT (var ∘ f)
  ren-subst′ f = ren-subst {f = f} λ x → refl

  subst-var∘old : ∀ {α b} → wkT {α} {α ▹ b} ~ substT (var ∘ old)
  subst-var∘old = ren-subst′ old

  ext' : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑
  ext' f (old x) = substT (var ∘ old) (f x)
  ext' f (new ._)     = var (new _)

  ext-ext' : ∀ {α β} (s : α ⇶ β)
             → ext s ~ ext' s
  ext-ext' s (old x) = subst-var∘old (s x)
  ext-ext' s (new ._) = refl


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


var-subst : ∀ {α} {β} {x} {f : α ⇶ β} {s : α → Tm α} → s ~ var → flip substT (s x) f == f x
var-subst {x = x} {s = s} s= with s x | s= x
var-subst s= | ._ | refl = refl

instance
  Tm-Monad : Monad Tm
  Tm-Monad = record
               {
                 _>>=_ = flip substT
               ; bind-assoc = subst-hom
               ; right-id = subst-var
               ; left-id = λ {α} {β} {x} {f} → var-subst
               ; fmap-bind = ren-subst
               }
joinT : ∀ {α} → Tm (Tm α) → Tm α
joinT = join

-- (>>=) f == join ∘ fmap f
-- TODO: generalise
subst-join∘ren : ∀ {α β} (s : α ⇶ β) → substT s ~ joinT ∘ renT s
subst-join∘ren s t =
  !(subst∘ren {f = s}{id}{id}{s} (λ x → ! renT-id′ (s x)) t
    ∙ renT-id′ _)


             {-
swpLams : ∀ {w} -> Tm w -> Tm w
swpLams (lam t0) = unpack Tm t0 (λ {v (lam t1) → unpack Tm t1 (λ v₁ t → lamP (λ x → lamP (λ x₁ → {!t [x := v1, x1 := v]!})))
                                   ;v t' → {!!}})
-- swpLams (lam (lam t0)) = {!!}
swpLams x = x
-}
{-
These should be derivable from the previous lemmas only:

join . fmap join     ≡ join . join
using subst-join∘ren and substsubst-var′

join . fmap return   ≡ join . return = id
using subst-join∘ren and subst-var′

join . fmap (fmap f) ≡ fmap f . join
-}
infix 0 _↝_ _~>_

data _↝_ {α} : (t u : Tm α) → Type where
  β     : ∀ {t u} → app (lam t) u ↝ [0≔ u ] t
  [_]·_ : ∀ {t t'}(r : t ↝ t') u → app t u ↝ app t'  u
  _·[_] : ∀ {t t'} u (r : t ↝ t') → app u t ↝ app u t'
  ƛ[_]  : ∀ {t t'}(r : t ↝ t') → lam t ↝ lam t'
_~>_ = _↝_


mutual
  Normal : ∀ {α} -> Tm α -> Set
  Normal (var x) = One
  Normal (lam tm) = Normal tm
  Normal (app t u) = Neutral t × Normal u

  Neutral : ∀ {α} -> Tm α -> Set
  Neutral (var x) = One
  Neutral (lam t) = Zero
  Neutral (app t u) = Neutral t × Normal u


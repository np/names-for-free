module Terms where

open import Sketch5
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)
open import Function

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

-- return . f ≡ fmap f . return
renT∘var : ∀ {α β} (f : α → β) → var ∘ f ~ renT f ∘ var
renT∘var f x = refl

wkT : ∀ {α β} {{s : α ⇉ β}} → Tm α → Tm β
wkT = renT wkN'
-- wkT : ∀ {α b} → Tm α → Tm (α ▹ b)
-- wkT = renT old
-- wkT : ∀ {α β} {{i : α ⊆ β}} → Tm α → Tm β
-- wkT = renT (wk …)

-- wkT : ∀ {α b} → Tm α → Tm (α ▹ b)
-- wkT = renT old
-- wkT : ∀ {α β} {{i : α ⊆ β}} → Tm α → Tm β
-- wkT = renT (wk …)

wkT' : ∀ {α β} (s : α ⇉ β) → Tm α → Tm β
wkT' (mk⇉ wk) = renT wk

η : ∀ {w} → Tm w → Tm w
η t = lamP λ x → app (wkT t) (var' x)

ext : ∀ {v w} (s : v ⇶ w) → v ⇑ ⇶ w ⇑
ext f (old x)  = wkT (f x)
ext f (new ._) = var (new ♦)

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
ext-var s= (new ._)     = refl

-- m >>= return   ≡   m
subst-var : ∀ {α}{s} (s= : s ~ var) → substT {α} s ~ id
subst-var s= (var x) = s= x
subst-var s= (lam t) = ap lam (subst-var (ext-var s=) t)
subst-var s= (app t u) = ap₂ app (subst-var s= t) (subst-var s= u)

subst-var′ : ∀ {α} → substT {α} var ~ id
subst-var′ = subst-var (λ _ → refl)

ext-ren-subst : ∀ {α β} {f : α → β}{s : α ⇶ β} (s= : (var ∘ f) ~ s) → (var ∘ map⇑ f) ~ ext s
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
instance
  Tm-Functor : Functor Tm
  Tm-Functor = record { _<$>_ = renT ; <$>-id = renT-id ; <$>-∘ = renT-∘ }
  Tm-Monad : Monad Tm
  Tm-Monad = record
               { return = var
               ; _>>=_ = λ x x₁ → substT x₁ x
               ; bind-assoc = subst-hom
               ; right-id = subst-var
               ; left-id = λ {α} {β} {x} {f} → refl
               }

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

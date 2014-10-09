module CPSBigStep where

open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat
open import Function
open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)

open import Sketch5
open import Terms
open import TermRed2

test = suc {!!}

open Term-Structure Tm-Monad hiding (_≔_; ext▹; ext)
open PointedRenaming using (_≔_ ; ext▹; ext)

load : ∀ {w b}  -> w -> w ▹ b -> w
load _ (old x) = x
load v (new _) = v



{-# NO_TERMINATION_CHECK #-}
mutual 
  psi : ∀ {a} -> Tm a -> Tm a
  psi (ƛ M) = lamP λ κ0 -> atVar Tm (cps M) κ0
  psi x = x

  cpsP : ∀ {a} -> Tm a -> ScopeP Tm a
  cpsP (M $$ N) κ0 = cps (wk {{box old}} M) $$
                         (lamP λ k1 →
                           cps (wk {{box (old ∘ old)}} N) $$
                               (lamP λ k2 ->
                                  (var' k2 $$ var' k1) $$ var' κ0))
  cpsP A κ0 = var' κ0 $$ (wk $ psi A) -- Or psi (wk A)

  cps : ∀ {a} -> Tm a -> Tm a
  cps A = lamP (cpsP A)

cps$$3 : ∀ {α} → ScopeP (ScopeP (ScopeP Tm)) α
cps$$3 κ0 k1 k2 = (var' k2 $$ var' k1) $$ var' κ0

cps$$2 : ∀ {α} → ScopeP (ScopeP Tm) α
cps$$2 κ0 k1 = lamP λ k2 → cps$$3 κ0 k1 k2

cpsP$$ : ∀ {α} → Tm α → ScopeP Tm α
cpsP$$ N κ0 = lamP λ k1 → cps (wk N) $$ cps$$2 κ0 k1

-- supposed to come for free
postulate
    cpsP-naturality : ∀ {α β} (f : α → β) (t : Tm α) → cpsP (renT f t) ♦ == renT (map⇑ f) (cpsP t ♦)
{-
cpsP-naturality f (var x) = refl
cpsP-naturality f (ƛ x) = ap (λ x₁ → var (new _) $$ ƛ (lam x₁)) {!!}
cpsP-naturality f (t $$ t₁) = {!!}
-}

-- cpsP-naturality : ∀ {α β b b'} (f : α → β) (t : Tm α) → cpsP (renT f t) b == renT (map▹ _ _ f) (cpsP t b')

-- supposed to come for free
cps-naturality : ∀ {α β} (f : α → β) (t : Tm α) → cps (renT f t) == renT f (cps t)
cps-naturality f t = ap lam (cpsP-naturality f t)

cpsP-wk-naturality : ∀ {α β} {{f : Box (α → β)}} (t : Tm α)
 → cpsP (wk {{f}} t) ♦ == wk {{box (map⇑ (unbox f))}} (cpsP t ♦)
cpsP-wk-naturality {{box f}} = cpsP-naturality f

open ≡-Reasoning

cps-Value : ∀ {α} (M : Tm α) → Value (cps M)
cps-Value M = ƛ (cpsP M ♦)

⟶-cps : ∀ {α} (M : Tm α) → cps M ⟶ cps M
⟶-cps M = ƛ (cpsP M ♦)

{-
  subst-lemma : ∀ {a b} {f g : a -> Tm b} P -> (∀ x -> f x ⟶ g x) ->  substT f P ⟶ substT g P
-}

instance
 postulate
  fun-ext : FunExt

-- these are provable because of fun-ext
map= : ∀ {a b} {f g : a -> b} (f=g : ∀ x -> f x == g x) P -> map f P == map g P
map= f=g (var x)  = ap var (f=g x)
map= f=g (ƛ t)    = ap ƛ_ (map= (map⇑= f=g) t)
map= f=g (t $$ u) = ap₂ _$$_ (map= f=g t) (map= f=g u)

ext= : ∀ {a b} {f g : a -> Tm b} (f=g : ∀ x -> f x == g x) (x : a ⇑) -> ext f x == ext g x
ext= f=g (old x) = ap (map old) (f=g x)
ext= f=g (new .♦) = refl

-- these are provable because of fun-ext
subst= : ∀ {a b} {f g : a -> Tm b} (f=g : ∀ x -> f x == g x) P ->  substT f P == substT g P
subst= f=g (var x)  = f=g x
subst= f=g (ƛ t)    = ap ƛ_ (subst= (ext= f=g) t)
subst= f=g (t $$ u) = ap2 _$$_ (subst= f=g t) (subst= f=g u)

foo : ∀ {α β γ} (s : β ⇶ γ) (f : α → β) t →
    [ ext s ] wk {{box (map⇑ f)}} t
    ==
    [ ext (s ∘ f) ] t
foo s f t =
    [ ext s ] wk {{box (map⇑ f)}} t
   ≡⟨ ap (λ z → [ ext s ] z) (map-bind' t) ⟩
    [ ext s ] [ var ∘′ map⇑ f ] t
   ≡⟨ bind-assoc (λ x → ext-map⇑' x) t ⟩
    [ ext (s ∘ f) ] t
   ∎

1≔_ : ∀ {α} → Tm α → (α ⇑^ 2) →K α ⇑
1≔ u = ext (0≔ u)

2≔_ : ∀ {α} → Tm α → (α ⇑^ 3) →K α ⇑^ 2
2≔ u = ext (1≔ u)

foo1 : ∀ {α} {u : Tm α} t → [ 1≔ u ] map (map⇑ old) t == t
foo1 t = subst-ext^-subst0-wk^-id 1

foo2 : ∀ {α} {u : Tm α} t → [ 2≔ u ] map (map⇑^ 2 old) t == t
foo2 t = subst-ext^-subst0-wk^-id 2

lem4 : ∀ {a} (x : a ▹ ♦) (t P : Tm (a ▹ ◆)) →
      (♦ ≔ ƛ (ƛ cpsP t ♦)) x ==
      (♦ ≔
       ƛ
       (ƛ
        substT (ext▹ ♦ ♦ (ext▹ ♦ ♦ (♦ ≔ ƛ P)))
        (renT (map▹ ♦ ♦ (map▹ ♦ ♦ (λ x₁ → old x₁))) (cpsP t ♦))))
      x
lem4 (old x) t P = refl
lem4 (new .♦) t P = ap ƛ_ (ap ƛ_ (! foo2 (cpsP t ♦)))

-- _·-⟶_ = flip ⟶-trans
open ⟶-Reasoning

⟶-psi : ∀ {α} {v : Tm α} → Value v → psi v ⟶ psi v
⟶-psi (ƛ t) = ƛ _

unƛ : ∀{α} {v : Tm α} → Value v → Tm (α ⇑)
unƛ (ƛ t) = t

⟶-psi' : ∀ {α} {v : Tm α} (val : Value v) → psi v ⟶ psi (ƛ unƛ val)
⟶-psi' (ƛ t) = ƛ _

lemma5' : ∀ {α} {M v : Tm α} (r : M ⟶ v) {P} → ([ 0≔ psi v ] P) ≈ ([ 0≔ ƛ P ] cpsP M ♦)
lemma5' {α} {v = v} (β {t} {t'} {u} {vu} ru rt rt') {P} {v'} rP
  = β (ƛ _) (ƛ _)
    (tr (λ x → x ⟶ v') pf
      (lemma5' {M = t} {ƛ t'} ru {t0'} {v'}
        (β (ƛ _) (ƛ _)
          (tr (λ x → x ⟶ v') pf'
             (lemma5' {M = u} rt
                (β (β (⟶-psi' (⟶-Value rt)) (ƛ _) (ƛ _)) (ƛ _)
                   (tr (λ x → x ⟶ v') pf''
                       (lemma5' {M = [ 0≔ vu ] t'} {v} rt' {P} rP))))))))
  where t00 = [ 1≔ ƛ P ] cps (wk u)
        t01 = [ 1≔ ƛ P ] cps$$2 ♦ ♦
        t0  = t00 $$ t01
        t00' = ƛ (wk {{box (map⇑ old)}} (cpsP u ♦))
        t01' = ƛ ((var (new ♦) $$ var (old (new ♦))) $$ (ƛ (map (map⇑ (old ∘ old)) P)))
        t0'  = t00' $$ t01'
        t00-pf = t00
               ≡⟨by-definition⟩
                 ([ 1≔ ƛ P ] cps (wk u))
               ≡⟨by-definition⟩
                 ƛ [ 2≔ ƛ P ] (cpsP (wk u) ♦)
               ≡⟨ ap (λ z → ƛ [ 2≔ ƛ P ] z) (cpsP-wk-naturality u) ⟩
                 ƛ [ 2≔ ƛ P ] wk {{box (map⇑ (old ∘ old))}} (cpsP u ♦)
               ≡⟨ ap ƛ_ (foo (1≔ ƛ P) (old ∘ old) (cpsP u ♦)) ⟩
                 ƛ [ ext (1≔ ƛ P ∘ old ∘ old) ] (cpsP u ♦)
               ≡⟨by-definition⟩
                 ƛ [ ext (var ∘′ old) ] (cpsP u ♦)
               ≡⟨ ap (λ s → ƛ [ s ] (cpsP u ♦)) (λ= (λ x → ! (! ext-return (λ _ → refl) _ ∙ ext-map⇑' {f = var} {g = old} x))) ⟩ -- We have a lemma for that I guess
                 ƛ [ var ∘′ map⇑ old ] (cpsP u ♦)
               ≡⟨ ap ƛ_ (! (map-bind' {f = map⇑ old} (cpsP u ♦))) ⟩
                 ƛ (map (map⇑ old) (cpsP u ♦))
               ≡⟨by-definition⟩
                 t00'
               ∎
        t01-pf = t01
               ≡⟨by-definition⟩
                 ƛ [ ext^ 2 (0≔ ƛ P) ] cps$$3 ♦ ♦ ♦
               ≡⟨by-definition⟩
                 ƛ [ ext^ 2 (0≔ ƛ P) ] ((var (new ♦) $$ var (old (new ♦))) $$ var (old (old (new ♦))))
               ≡⟨by-definition⟩
                 ƛ ((var (new ♦) $$ var (old (new ♦))) $$ (ƛ (map (map⇑ old) (map (map⇑ old) P))))
               ≡⟨ ap (λ z → ƛ ((var (new ♦) $$ var (old (new ♦))) $$ ƛ z)) (<$>-∘ map⇑-∘' P) ⟩
                 ƛ ((var (new ♦) $$ var (old (new ♦))) $$ (ƛ (map (map⇑ (old ∘ old)) P)))
                 {-
               ≡⟨ ? ⟩
                 lamP λ k2 → (var' k2 $$ var (old (new ♦))) $$ (ƛ (map (map⇑ (old ∘ old)) P))
                 -}
               ∎
        pf = [ 0≔ ƛ t0' ] (cpsP t ♦)
           ≡⟨ ap (λ z → [ 0≔ ƛ z ] cpsP t ♦) (ap₂ _$$_ (! t00-pf) (! t01-pf)) ⟩
             [ 0≔ ƛ t0 ] (cpsP t ♦)
           ≡⟨ ap (λ z → [ 0≔ ƛ t0 ] z) (! foo1 (cpsP t ♦)) ⟩
             [ 0≔ ƛ t0 ] [ 1≔ ƛ P ] wk {{box (map⇑ old)}} (cpsP t ♦)
           ≡⟨ ap (λ z → [ 0≔ ƛ t0 ] [ 1≔ ƛ P ] z) (! cpsP-wk-naturality t) ⟩
             [ 0≔ ƛ t0 ] [ 1≔ ƛ P ] (cpsP (wk t) ♦)
           ∎
        t11 = ƛ([ 1≔ psi (ƛ t') ]
                       ((var (new ♦) $$ var (old (new ♦))) $$
                        ƛ map (map⇑ (old ∘ old)) P))
        t111 = ƛ [ 2≔ psi (ƛ t') ] map (map⇑ (old ∘ old)) P
        t111' = ƛ (map (map⇑ old) P)
        t111-pf = t111
                ≡⟨ ap ƛ_ (foo (1≔ psi (ƛ t')) (old ∘ old) P) ⟩
                  ƛ [ ext (1≔ psi (ƛ t') ∘ old ∘ old) ] P
                ≡⟨by-definition⟩
                  ƛ [ ext (var ∘′ old) ] P
                ≡⟨ ap (λ s → ƛ [ s ] P) (λ= λ x → ! ext-ren-subst' {f = old} x) ⟩
                  ƛ [ var ∘′ map⇑ old ] P
                ≡⟨ ap ƛ_ (! map-bind' {f = map⇑ old} P) ⟩
                  t111'
                ∎
        t110  = var (new ♦) $$ (ƛ(ƛ(map (map⇑^ 2 old) (cpsP t' ♦))))
        t11'  = ƛ(t110 $$ t111)
        t11'' = ƛ(t110 $$ t111')
        pf' = [ 0≔ t11'' ] (cpsP u ♦)
            ≡⟨ ap (λ z → [ 0≔ ƛ (t110 $$ z) ] (cpsP u ♦)) (! t111-pf) ⟩
              [ 0≔ t11' ] (cpsP u ♦)
            ≡⟨ refl ⟩
              [ 0≔ t11 ] (cpsP u ♦)
            ≡⟨ ap (λ z → [ 0≔ t11 ] z) (! foo1 (cpsP u ♦)) ⟩
              [ 0≔ t11 ]
              [ 1≔ ƛ (ƛ (cpsP t' ♦)) ]
              map (map⇑ old) (cpsP u ♦)
            ∎
        pf'' = [ 0≔ ƛ P ] cpsP ([ 0≔ vu ] t') ♦
             ≡⟨ {!!} ⟩ -- <= they might not be equal be reducing to the same thing
               [ 0≔ ƛ P ]
               [ 1≔ ƛ(ƛ (cpsP t' ♦)) ]
               cpsP (unƛ (⟶-Value rt)) ♦
             ≡⟨ ap (λ z → [ 0≔ ƛ P ]
                    [ 1≔ ƛ(ƛ z) ]
                    cpsP (unƛ (⟶-Value rt)) ♦) (! foo2 (cpsP t' ♦)) ⟩
               [ 0≔ ƛ P ]
               [ 1≔ ƛ([ 1≔ psi vu ] (ƛ map (map⇑^ 2 old) (cpsP t' ♦))) ]
               cpsP (unƛ (⟶-Value rt)) ♦
             ≡⟨ ap (λ z → [ 0≔ ƛ z ]
                   [ 1≔ ƛ([ 1≔ psi vu ] (ƛ map (map⇑^ 2 old) (cpsP t' ♦))) ]
                   cpsP (unƛ (⟶-Value rt)) ♦) (! foo1 P) ⟩
               [ 0≔ ƛ([ 1≔ psi vu ] (map (map⇑ old) P)) ]
               [ 1≔ ƛ([ 1≔ psi vu ] (ƛ map (map⇑^ 2 old) (cpsP t' ♦))) ]
               cpsP (unƛ (⟶-Value rt)) ♦
             ∎
lemma5' (ƛ t) {P} {v} rP = β (ƛ _) (ƛ _) (tr (λ x → x ⟶ v) (subst= (λ { x → lem4 x t P }) P) rP)

-- (⟶-trans (subst-lemma P
--    (λ { (old x) → {!!}
--       ; (new .♦) → {!!} })) rP)  
{-
  -}

lemma5 : ∀{a} {M v : Tm a} {P : ScopeF Tm a} → (M ⟶ v) → ([ 0≔ psi v ] P) ≈ (cps M $$ ƛ P)
lemma5 {M = M} r r' = β (⟶-cps M) (ƛ _) (lemma5' r r')

theorem : ∀{a} (M v : Tm a) → M ⟶ v → cps M $$ idTm ⟶ psi v
theorem M v r = lemma5 {M = M} {v = v} {P = var (new ◆)} r (⟶-psi (⟶-Value r))
-- -}
-- -}
-- -}
-- -}

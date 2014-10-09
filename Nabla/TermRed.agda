module TermRed where

open import Function
open import Function.Extensionality
open import Relation.Binary.NP
open import Relation.Binary.PropositionalEquality.NP
  hiding ([_])
  renaming (_≡_ to _==_; _≗_ to _~_)

open import Sketch5
open import Terms

open Term-Structure Tm-Monad

-- Not used yet
mutual
    -- Neutral forms
    data Neu {α} : Tm α → Type where
      var  : ∀ x → Neu (var x)
      _$$_ : ∀ {t u} → Neu t → Nrm u → Neu (t $$ u)

    -- Normal forms
    data Nrm {α} : Tm α → Type where
      ƛ_  : {t : Tm (α ⇑)} → Nrm t → Nrm (ƛ t)
      neu : ∀ {t} → Neu t → Nrm t

infix 2 _⟶_
data _⟶_ {α} : (t u : Tm α) → Type where
  -- nrm : ∀{v} → Nrm v → v ⟶ v
  noop  : ∀{v} → v ⟶ v
  β    : ∀ {t u v} → [ 0≔ u ] t ⟶ v -> ƛ t $$ u ⟶ v
  _$$_ : ∀ {t t' u u'}(r : t ⟶ t') (q : u ⟶ u') -> t $$ u ⟶ t' $$ u'
  ƛ_   : ∀ {t t'}(r : t ⟶ t') → ƛ t ⟶ ƛ t'

module _ {α : World} where

    _≈_ : ∀ (t u : Tm α) → Type
    t ≈ u = ∀ {v} → t ⟶ v → u ⟶ v

    ≈-refl : Reflexive _≈_
    ≈-refl = id

    ≈-trans : Transitive _≈_
    ≈-trans p q = q ∘ p

    module ≈-Reasoning = Refl-Trans-Reasoning _≈_ ≈-refl ≈-trans

    β-≈ : ∀ {t} {u : Tm α} → [ 0≔ u ] t ≈ (ƛ t $$ u)
    β-≈ = β

    ≈-reflexive : ∀ {t u : Tm α} -> (t == u) -> (t ≈ u)
    ≈-reflexive refl x = x

    ≈-⟶ : ∀ {t u : Tm α} -> (t ≈ u) -> u ⟶ t
    ≈-⟶ p = p noop

infix 2 _⟶°_
_⟶°_ : ∀ {α β}(s s' : α ⇶ β) → Type
s ⟶° s' = ∀ x → s x ⟶ s' x

0≔⟶° : ∀ {α} {M v : Tm α} (r : M ⟶ v) → 0≔ M ⟶° 0≔ v
0≔⟶° r (old x)  = noop
0≔⟶° r (new .♦) = r

module _ {{_ : FunExt}} where
    open ≡-Reasoning

    map⟶ : ∀ {a b} {f : a -> b} {f' : a -> b} (f= : f ~ f') {t u : Tm a} -> (t ⟶ u) -> f <$> t ⟶ f' <$> u
    map⟶ f= noop = ≈-reflexive (ap (λ f → f <$> _) (λ= (!_ ∘ f=))) noop
    map⟶ {f = f} {f'} f= (β {t} {u} {v} r) = β (tr id (! pf) (map⟶ f= r))
      where pf = (0≔ (f <$> u) =<< (map⇑ f <$> t) ⟶ f' <$> v)
               ≡⟨ ap (λ x → x ⟶ f' <$> v) (=<<-<$> t) ⟩
                 ((0≔ (f <$> u) ∘ map⇑ f) =<< t ⟶ f' <$> v)
               ≡⟨ ap (λ x → x =<< t ⟶ f' <$> v) (λ= (0≔-map f u)) ⟩
                 (map f ∘ 0≔ u =<< t ⟶ f' <$> v)
               ≡⟨ ap (λ x → x ⟶ f' <$> v) (! <$>-=<< t) ⟩
                 (f <$> 0≔ u =<< t ⟶ f' <$> v)
               ∎
    map⟶ f= (r1 $$ r2) = map⟶ f= r1 $$ map⟶ f= r2
    map⟶ f= (ƛ r) = ƛ map⟶ (map⇑= f=) r

    ext⟶ : ∀ {a b} {s s' : a ⇶ b} -> (s ⟶° s') -> (ext s ⟶° ext s')
    ext⟶ s= (old x) = map⟶ (λ x₁ → refl) (s= x)
    ext⟶ s= (new .♦) = noop

    subst⟶°1 : ∀ {a b} {s s' : a ⇶ b} -> (s ⟶° s') -> substT s ⟶° substT s'
    subst⟶°1 s= (var x)  = s= x
    subst⟶°1 s= (ƛ M)    = ƛ (subst⟶°1 (ext⟶ s=) M)
    subst⟶°1 s= (M $$ N) = subst⟶°1 s= M $$ subst⟶°1 s= N

    subst⟶ : ∀ {a b} {M M' : Tm a} {s s' : a ⇶ b} → (M ⟶ M') → (s ⟶° s') → M >>= s ⟶ M' >>= s'
    subst⟶ {M = M} noop x = subst⟶°1 x M
    subst⟶ (β {t} r1) x =
      β (≈-reflexive (bind-assoc' t ∙ ! ap (_>>=_ t) (λ= subst0-ext) ∙ ! bind-assoc' t) (subst⟶ r1 x))
    subst⟶ (r1 $$ r2) x = subst⟶ r1 x $$ subst⟶ r2 x
    subst⟶ (ƛ r1) x = ƛ subst⟶ r1 (ext⟶ x)

    subst-lemma : ∀ {a} {M v : Tm a} {N v' : ScopeF Tm a} (rM : M ⟶ v) (rN : N ⟶ v') -> [ 0≔ M ] N ⟶ [ 0≔ v ] v'
    subst-lemma rM rN = subst⟶ rN (0≔⟶° rM)
-- -}
-- -}
-- -}
-- -}



-- Potentially relevant:
-- http://gallium.inria.fr/~xleroy/publi/cps-dargaye-leroy.pdf
-- http://crpit.com/confpapers/CRPITV51Tian.pdf

module CPS where

open import Data.List
open import Data.Product hiding (map)
open import Data.Maybe hiding (module Eq; Eq; map)
open import Data.Nat
open import Function

open import Sketch5
open Example-TmFresh


mutual
  data TmC a : Type where
    HaltC : Value a -> TmC a
    AppC : Value a -> Value a -> TmC a
    LetC : Value a -> ScopeF TmC a -> TmC a

  data Value a : Type where
    LamC : ScopeF TmC a -> Value a
    PairC : Value a -> Value a -> Value a
    VarC FstC SndC : a -> Value a


mutual
 _<$C>_ : ∀ {A B} → (A → B) → TmC A → TmC B
 f <$C> HaltC x = HaltC (f <$V> x)
 f <$C> AppC x x₁ = AppC (f <$V> x) (f <$V> x₁)
 f <$C> LetC x u = LetC (f <$V> x) (map▹ ♦ ♦ f <$C> u)
 
 _<$V>_ : ∀ {A B} → (A → B) → Value A → Value B
 f <$V> LamC x = LamC (map▹ ♦ ♦ f <$C> x)
 f <$V> PairC t u = PairC (f <$V> t) (f <$V> u)
 f <$V> VarC x = VarC (f x)
 f <$V> FstC x = FstC (f x)
 f <$V> SndC x = SndC (f x)

instance
  tmCFun : Functor TmC
  tmCFun = record { _<$>_ = _<$C>_ ; <$>-id = {!!} ; <$>-∘ = {!!} }

wkC : ∀ {α β} {{s : α ⇉ β}} → TmC α → TmC β
wkC {{s = mk⇉ f}} = _<$C>_ f


load : ∀ {w b}  -> w -> w ▹ b -> w
load _ (old x) = x
load v (new _) = v

cps : ∀ {a} -> Tm a -> ScopeF TmC a -> TmC a
cps (var x) k = load x <$C> k
cps (lam e) k = LetC (LamC (pack TmC λ p →
                        LetC (FstC (name' p)) (pack TmC λ x1 →
                        LetC (SndC (name' p)) (pack TmC λ x2 →
                        cps (wk (atVar Tm e p)) (pack TmC λ r →
                          AppC (VarC (name' x2)) (VarC (name' r))))))) k
cps (app e1 e2) k = cps (   e1) (pack TmC λ x₁ →
                    cps (wk e2) (pack TmC λ x₂ →
                    AppC (VarC (name' x₁))
                         (PairC (VarC (name' x₂))
                                (LamC (pack TmC (λ x → atVar' TmC k x))))))


-- untag : ∀ {a} -> a ⊎ a -> a
-- untag (left x) = x
-- untag (right x) = x
-- fixit : ∀ {a} -> (a ⊎ Binder a) -> (a ▹ ◆)
-- fixit (left x) = old x
-- fixit (right x) = new ♦


-- cps : ∀ {a} -> Tm a -> (∀ {v} -> v -> TmC (a ⊎ v)) -> TmC a
-- cps (var x) k = untag <$C> k x
-- cps (lam e) k = LetC (LamC (pack TmC \ p ->
--                         LetC (FstC (name' p)) (pack TmC (λ x1 →
--                         LetC (SndC (name' p)) (pack TmC (λ x2 →
--                         cps ( wkT' ⇉-skip {! atVar Tm e x1 !} ) (λ r →
--                         AppC (VarC (left (name' x2))) (VarC (right r))))))))) (fixit <$C> k ◆)
-- cps (app e1 e2) k = cps e1   λ x1 →
--                     cps {!wk e2!} λ x2 →
--                     AppC (VarC (left (right x1)))
--                          (PairC (VarC (right x2))
--                                 (LamC (pack TmC (λ x → {!k x!}))))

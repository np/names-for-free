
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

_<$C>_ : ∀ {A B} → (A → B) → TmC A → TmC B
_<$C>_ = {!!}

untag : ∀ {a} -> a ⊎ a -> a
untag (left x) = x
untag (right x) = x

fixit : ∀ {a} -> (a ⊎ Binder a) -> (a ▹ ◆)
fixit = {!!}


cps : ∀ {a} -> Tm a -> (∀ {v} -> v -> TmC (a ⊎ v)) -> TmC a
cps (var x) k = untag <$C> k x
cps (lam e) k = LetC (LamC (pack TmC \ p ->
                        LetC (FstC (name' p)) (pack TmC (λ x1 →
                        LetC (SndC (name' p)) (pack TmC (λ x2 →
                        cps ( wkT' ⇉-skip {! atVar Tm e x1 !} ) (λ r →
                        AppC (VarC (left (name' x2))) (VarC (right r))))))))) (fixit <$C> k ◆)
cps (app e1 e2) k = cps e1   λ x1 →
                    cps {!wk e2!} λ x2 →
                    AppC (VarC (left (right x1)))
                         (PairC (VarC (right x2))
                                (LamC (pack TmC (λ x → {!k x!}))))

open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP renaming (_≡_ to _==_)

Type = Set
Type1 = Set1

… : {A : Type} {{x : A}} → A
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

Π : (A : Type) (B : A → Type) → Type
Π A B = (x : A) → B x

record Σ (A : Type) (B : A → Type) : Type where
  constructor _,_
  field
    fst : A
    snd : B fst
open  Σ

{-
data _==_ {A : Type} (a : A) : (b : A) → Type where
  refl : a == a

cong : ∀ {A B} {x y : A} (f : A → B) → x == y → f x == f y
cong f refl = refl
-}

record Interface : Set1 where
  infixr 5 _▹_
  infix 3 _⊆_
  field
    World : Set -- what I'd call a context of names
    Binder : World → Set     -- type of a binder fresh for w. ('b:Binder w' could be written 'b∉w')
    Name : World → Set -- aka. reference into a world
    _▹_ : (w : World) → Binder w → World -- extend a world
 
  NablaP : ∀ w → (T : World → Set) → Set
  NablaP w T = Π (Binder w) \ b -> T (w ▹ b)

  NablaS : ∀ w → (T : World → Set) → Set
  NablaS w T = Σ (Binder w) \ b -> T (w ▹ b)

  
  field
    -- Scopes -- Representations of ∇(b∉w). T[b]
    pack   : (T : World → Set) {w : World} → NablaP w T → NablaS w T
    unpack : (T : World → Set) {w : World} → NablaS w T → NablaP w T
    -- Alternative is to use an abstract scope (Nabla) as actual representation; possibly more accurate than both the above.
      -- Nabla : ∀ w → (T : Binder w → Set) → Set
      -- toPi   : ∀ {w T} -> Nabla w T -> Π(Binder w) T
      -- fromPi : ∀ {w T} -> Π(Binder w) T -> Nabla w T 
      -- etc.


    -- no  need for the empty world; we can quantify on all worlds.

    -- refer a specific binder
    name : ∀ {w} → (b : Binder w) → Name (w ▹ b)

    -- Names are comparable and exportable
    _==N_ : ∀ {α} (x y : Name α) → Bool
    -- exportN : ∀ {α b} → (n : Name (α ▹ b)) → T (name b ==N n) ⊎ (Name α)
    exportN : ∀ {α b} → (n : Name (α ▹ b)) → (name b == n) ⊎ (Name α)

    exportN-name : ∀ {α} (b : Binder α) → exportN (name b) == left refl

    -- no need for the fresh for relation.

    _⊆_  : (v w : World) → Set
    
    wkN : ∀ {α β} → (α ⊆ β) → Name   α → Name   β -- better: subtyping
    wkB : ∀ {α β} → (α ⊆ β) → Binder β → Binder α

    ⊆-refl : ∀ {w} → w ⊆ w
    ⊆-▹ :  ∀ {α β} b → (s : α ⊆ β) → (α ▹ wkB s b) ⊆ ( β ▹ b )

    -- in nompa, skip took a "b # α", now # is folded
    ⊆-skip :  ∀ {α} b → α ⊆ ( α ▹ b )

      -- + swap if necessary

    _⇉_  : (v w : World) → Set

    renN : ∀ {α β} → (α ⇉ β) → Name   α → Name   β
    renB : ∀ {α β} → (α ⇉ β) → Binder β → Binder α

    ⇉-refl : ∀ {w} → w ⇉ w
    ⇉-▹    :  ∀ {α β} (b : Binder α) (b' : Binder β) → (s : α ⇉ β) → (α ▹ b) ⇉ (β ▹ b')
    ⇉-skip :  ∀ {α} b → α ⇉ (α ▹ b)

    sucB : ∀ {w} (b : Binder w) → Binder (w ▹ b)

  record _⊆'_ (α β : World) : Set where
    constructor mk⊆'
    field
      get⊆' : α ⊆ β
  open _⊆'_

  wkB' : ∀ {α β} {{s : α ⊆' β}} → Binder β → Binder α
  wkB' = wkB (get⊆' …)

  instance
    ⊆-skip' :  ∀ {α} {b} → α ⊆' ( α ▹ b )
    ⊆-skip' = mk⊆' (⊆-skip _)

    ⊆-refl' : ∀ {w} → w ⊆' w
    ⊆-refl' = mk⊆' ⊆-refl

    ⊆-▹' :  ∀ {α β}{b}{{s : α ⊆' β}} → (α ▹ wkB' b) ⊆' ( β ▹ b )
    ⊆-▹' {{mk⊆' s}} = mk⊆' (⊆-▹ _ s)

  wkN' : ∀ {α β} {{s : α ⊆' β}} → Name   α → Name   β -- better: subtyping
  wkN' = wkN (get⊆' …)

  name' : ∀ {w w'}(b : Binder w) {{s : (w ▹ b) ⊆' w'}} → Name w'
  name' b = wkN' (name b)


  record SubstEnv (Res : World → Type) (α β : World) : Type where
    constructor mk
    field
      trName : Name α → Res β
      seed   : Binder β

    trBinder : Binder α → Binder β
    trBinder _ = seed

  open SubstEnv public


module Example (i : Interface) where
  open Interface i

  data Tm (w : World) : Type where
    var : Name w -> Tm w
    lam : NablaS w Tm -> Tm w
    app : Tm w -> Tm w -> Tm w

  lamP : ∀ {w} → NablaP w Tm -> Tm w
  lamP f = lam (pack Tm f)

  var' : ∀ {w w'}(b : Binder w){{s : (w ▹ b) ⊆' w'}} → Tm w'
  var' b = var (name' b)

  {-
  renT : ∀ {α β} → (α ⇉ β) → Tm α → Tm β
  renT f (var x) = var (renN f x)
  -- NablaP: renT f (lam x) = lam (λ y → renT (⇉-▹ (renB f y) y f) (x (renB f y)))
  renT f (lam (b , t)) = lam ({!!} , {!renT (⇉-▹ (renB f b) b t)!}) -- (λ y → renT (⇉-▹ (renB f y) y f) (x (renB f y)))
  renT f (app t u) = app (renT f t) (renT f u)
-}

  {-# NO_TERMINATION_CHECK #-}
  wkT : ∀ {α β} {{s : α ⊆' β}} → Tm α → Tm β
  wkT (var x) = var (wkN' x)
  -- wkT (lam f) = lam (λ x → wkT (f (wkB' x))) -- TODO wkNablaP
  wkT (lam t) = lamP λ b' → wkT (unpack Tm t (wkB' b'))
  wkT (app t u) = app (wkT t) (wkT u)

  wkT' : ∀ {α β} (s : α ⊆ β) → Tm α → Tm β
  wkT' s = wkT {{mk⊆' s}}

  -- α ⇉ β → α ⇶ β

  _⇶_ = SubstEnv Tm

  substN = trName

  ext : ∀ {v w b} (s : v ⇶ w) → (v ▹ b) ⇶ (w ▹ seed s)
  ext {v} {w} {b} (mk f seed) = mk (λ x → g (exportN x)) (sucB seed)
    where g : ∀ {x} → (name b == x) ⊎ (Name v) → Tm (w ▹ seed)
          g (left x) = var (name seed)
          g (right n) = wkT' (⊆-skip seed) (f n)

  {-# NO_TERMINATION_CHECK #-}
  substT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
  substT s (var x) = substN s x
  -- substT s (lam x) = lam (unpack {T = Tm} (_ , substT (ext s) (snd (pack {T = Tm} x))))
  substT s (lam (b , t)) = lam (_ , substT (ext s) t)
  substT s (app t u) = app (substT s t) (substT s u)

  _∘_ : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) → α ⇶ γ
  s ∘ s' = mk (λ x → substT s (trName s' x)) (seed s)

  {-
  unpack= : ∀ {T : World → Type} {w b b'} {t : T (w ▹ b)} {t' : T (w ▹ b')} → t == t' → unpack {T} (b , t) == unpack {T} (b , t')
  unpack= e = {!!}
-}

  _~_ : ∀ {α β} (s s' : α ⇶ β) → Type
  s ~ s' = ∀ t → substT s t == substT s' t

  -- exportN (wkN i x)

  foo : ∀ {w} s i t → substT (ext {w} s) (wkT {{i}} t) == wkT {{i}} (substT s t)
  foo s i (var x) = {!!}
  foo s i (lam (b , t)) = {!!}
  foo s i (app t u) = {!!}

  ext-hom' : ∀ {α β γ} b (s : β ⇶ γ) (s' : α ⇶ β) → (ext s ∘ ext {b = b} s') ~ ext (s ∘ s')
  ext-hom' b s s' (var x) with exportN x
  ext-hom' b s s' (var x) | left x₁ rewrite exportN-name (seed s') = refl
  ext-hom' b s s' (var x) | right x₁ = {!foo s!}
  ext-hom' b s s' (lam (b' , t)) = {!!}
  ext-hom' b s s' (app t u) = {!!}

  ext-hom : ∀ {α β γ} b (s : β ⇶ γ) (s' : α ⇶ β) → (ext s ∘ ext {b = b} s') == ext (s ∘ s')
  ext-hom b s s' = ap (λ f → mk f (sucB (seed s))) {!!}

  -- ext-hom' b s s' = ap (λ z → substT z t) (ext-hom b s s')

  {-
  packunpack : ∀ {T w} (x : NablaS w T) → pack T (unpack T x) == x
  packunpack = {!!}
  -}


  {-
  subst : ∀ {A} {x y : A}(P : A → Type) → x == y → P x → P y
  subst P refl x₁ = x₁
  -}

  pair= : ∀ {A} {B : A → Type} {p q : Σ A B} (e : fst p == fst q) → tr B e (snd p) == snd q → p == q
  pair= {p = fst , snd} {.fst , snd₁} refl eq = cong (_,_ fst) eq

  substT-hom : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) t → substT s (substT s' t) == substT (s ∘ s') t
  substT-hom s s' (var x) = refl
  substT-hom s s' (lam (b , t)) =
    ap lam (pair= refl (substT-hom (ext s) (ext s') t ∙ ext-hom' b s s' t))
  substT-hom s s' (app t u) = ap₂ app (substT-hom s s' t) (substT-hom s s' u)

  {-
  id : ∀ {w} -> Tm w
  id = lam λ x → var (name x)

  ap'' : ∀ {w} -> Tm w
  ap'' = lam λ x → lam λ y → app (var' x) (var' y)

  η : ∀ {w} → Tm w → Tm w
  η t = lam λ x → app (wkT t) (var' x)

  ap' : ∀ {w} -> NablaP w (λ w' → NablaP w' Tm)
  ap' = λ x → λ y → app (var (wkN (⊆-skip y) (name x))) (var (name y))

  {- invalid!
  foo : ∀ {w} (b : Binder w) → Tm ((w ▹ b) ▹ b)
  foo = λ b → ap' b b
  -}
  
mutual
  data Ctx : Set where
    nil : Ctx
    cons : (c : Ctx) -> Bnd c -> Ctx -- we could do everything with just nats.

  Bnd : Ctx -> Set
  Bnd _ = One

data Idx : Ctx -> Set where
  here : ∀ {c b} -> Idx (cons c b)
  there : ∀ {c b} -> Idx c -> Idx (cons c b)

_==i_ : ∀ {α} (x y : Idx α) → Bool
here ==i here = true
here ==i there y = false
there x ==i here = false
there x ==i there y = x ==i y

{-
exportI : ∀ {α b} → (n : Idx (cons α b)) → T (here ==i n) ⊎ (Idx α)
exportI {b = tt} here = left tt
exportI {b = tt} (there n) = right n
-}

exportI : ∀ {α b} → (n : Idx (cons α b)) → (here == n) ⊎ (Idx α)
exportI {b = tt} here = left refl
exportI {b = tt} (there n) = right n

data _incl_ : Ctx -> Ctx -> Set where
  done : ∀ {c} -> nil incl c
  skip  : ∀ {v w b} -> v incl w -> v incl (cons w b)
  take  : ∀ {v w b} -> v incl w -> (cons v b) incl (cons w b)

wkI : ∀ {v w} -> v incl w -> Idx v -> Idx w
wkI done ()
wkI (skip p) i = there (wkI p i)
wkI (take p) i = here

incl-refl : ∀ {w} → w incl w
incl-refl {nil} = done
incl-refl {cons w x} = take incl-refl

incl-cons :  ∀ {α β} b → (s : α incl β) → (cons α b) incl ( cons  β b )
incl-cons b = take

incl-skip :  ∀ {α} b → α incl ( cons  α b )
incl-skip b = skip incl-refl

implem : Interface
implem = record
           { World = Ctx
           ; Binder = Bnd
           ; Name = Idx
           ; _▹_ = cons
           ; pack = λ f → record { fst = tt ; snd = f tt }
           ; unpack = λ b x → snd b
           ; name = λ b → here
           ; _==N_ = _==i_
           ; exportN = exportI
           ; _⊆_ = _incl_
           ; wkN = wkI
           ; wkB = λ x x₁ → tt
           ; ⊆-refl = incl-refl
           ; ⊆-▹ = incl-cons
           ; ⊆-skip = incl-skip
           ; _⇉_ = _incl_
           ; renN = wkI
           ; ⇉-refl = incl-refl
           ; ⇉-▹ = λ _ _ → take
           ; ⇉-skip = incl-skip
           }
-- -}
-- -}
-- -}

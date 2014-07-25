{-# OPTIONS --type-in-type #-}
Type = Set
Type1 = Set1

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
    p1 : A
    p2 : B p1
open  Σ

data _==_ {A : Type} (a : A) : (b : A) → Type where
  refl : a == a

record Interface : Set1 where
  infixr 5 _▹_
  infix 3 _⊆_
  field
    World : Set -- what I'd call a context of names
    Binder : World → Set     -- type of a binder fresh for w. ('b:Binder w' could be written 'b∉w')
    Name : World → Set -- aka. reference into a world
    _▹_ : (w : World) → Binder w → World -- extend a world

    -- Scopes -- Representations of ∇(b∉w). T[b]
    pack   : ∀ {w} → {T : Binder w → Set} → Π(Binder w) T → Σ(Binder w) T
    unpack : ∀ {w} → {T : Binder w → Set} → Σ(Binder w) T → Π(Binder w) T
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
    exportN : ∀ {α b} → (n : Name (α ▹ b)) → T (name b ==N n) ⊎ (Name α)

    -- no need for the fresh for relation.

    _⊆_  : (v w : World) → Set
    
    wkN : ∀ {α β} → (α ⊆ β) → Name   α → Name   β -- better: subtyping
    wkB : ∀ {α β} → (α ⊆ β) → Binder β → Binder α

    ⊆-refl : ∀ {w} → w ⊆ w
    ⊆-▹ :  ∀ {α β} b → (s : α ⊆ β) → (α ▹ wkB s b) ⊆ ( β ▹ b )
    ⊆-skip :  ∀ {α} b → α ⊆ ( α ▹ b )
      -- + swap if necessary

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

exportI : ∀ {α b} → (n : Idx (cons α b)) → T (here ==i n) ⊎ (Idx α)
exportI {b = tt} here = left tt
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
           ; pack = λ f → record { p1 = tt ; p2 = f tt }
           ; unpack = λ b x → p2 b
           ; name = λ b → here
           ; _==N_ = _==i_
           ; exportN = exportI
           ; _⊆_ = _incl_
           ; wkN = wkI
           ; wkB = λ x x₁ → tt
           ; ⊆-refl = incl-refl
           ; ⊆-▹ = incl-cons
           ; ⊆-skip = incl-skip
           }

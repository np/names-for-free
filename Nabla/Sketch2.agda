Type = Set
Type1 = Set1

data Bool : Type where
  true false : Bool

data _⊎_ (A : Type)(B : Type) : Type where
  left : A -> A ⊎ B
  right : B -> A ⊎ B

Π : (A : Type) (B : A -> Type) -> Type
Π A B = (x : A) -> B x

record Σ (A : Type) (B : A -> Type) : Type where
  field
    p1 : A
    p2 : B p1

data _==_ {A : Type} (a : A) : (b : A) -> Type where
  refl : a == a

record Interface : Set1 where
  infixr 5 _/_
  infix 3 _⊆_
  field
    -- minimal kit to define types
    World : Set -- what I'd call a context of names
    Binder : World -> Set     -- type of a binder fresh for w. ('b:Binder w' could be written 'b∉w')
    Name : World → Set -- what I'd call a reference
    _/_ : (w : World) → Binder w → World -- extend a world

    -- Scopes -- Representations of ∇(b∉w). t[b]
    pack   : ∀ {w} -> {T : Binder w -> Set} -> Π (Binder w) T -> Σ(Binder w) T
    unpack : ∀ {w} -> {T : Binder w -> Set} -> Σ(Binder w) T -> Π(Binder w) T
    -- Alternative is to use an abstract scope (Nabla) as actual representation; possibly more accurate than both the above.
    -- Nabla :{T : Binder w -> Set} -> (b:Binder w) -> T b -> Set


    -- no  need for the empty world; we can quantify on all worlds.

    -- refer a specific binder
    name : ∀ {w} -> (b : Binder w) -> Name (w / b)

    -- Names are comparable and exportable
    ==N : ∀ {α} (x y : Name α) → Bool
    exportN : ∀ {α b} → (n : Name (α / b)) → (name b == n) ⊎ (Name α)

    -- no need for the fresh for relation.

  data _⊆_  : (v w : World) -> Set where
      ⊆-refl : ∀ {w} -> w ⊆ w
      ⊆-/ :  ∀ {α β} b → α ⊆ β → α ⊆ ( β / b )
      -- ⊆-skip :  ∀ {α} b → α ⊆ ( α / b )
      -- + swap if necessary

  -- field
  --    coerceN : ∀ {α β} → (α ⊆ β) → Name   α → Name   β
  --    coerceB : ∀ {α β} → (α ⊆ β) → Binder β → Binder α

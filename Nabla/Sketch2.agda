record Interface : Set1 where
  infixr 5 /
  infix 3 ⊆
  field
    -- minimal kit to define types
    World : Set -- what I'd call a context of names
    Binder : (w : World) -> Set     -- a new binder fresh for w. ('b:Binder w' could be written 'b∉w')
    Name : World → Set -- what I'd call a reference
    / : (w : World) → Binder w → World

    -- Scopes -- Representations of ∇(b∉w). t[b]
    pack   : {T : Binder w -> Set} -> Π(b:Binder w) (T b) -> Σ(b:Binder w) (T b)
    unpack : {T : Binder w -> Set} -> Σ(b:Binder w) (T b) -> Π(b:Binder w) (T b)
    -- Alternative is to use an abstract scope (Nabla) as actual representation; possibly more accurate than both the above.
    -- Nabla :{T : Binder w -> Set} -> (b:Binder w) -> T b -> Set


    -- no  need for the empty world; we can quantify on all worlds.

    -- referring a specific binder
    name : (b : Binder w) -> Name (w / b)

    -- Names are comparable and exportable
    ==N : ∀ {α} (x y : Name α) → Bool
    exportN : ∀ {α b} → (n : Name (b / α)) → (name b == n) ∪ (Name α)

    -- no need for the fresh for relation.

    ⊆-trans : Transitive ⊆

  data v ⊆ w : Set where
      ⊆-refl : w ⊆ w
      ⊆-/ :  ∀ {α β} b → α ⊆ β → ( b / α) ⊆ ( b / β )
      ⊆-skip :  ∀ {α} b → α ⊆ ( b / α )
      -- + swap if necessary

  field
     coerceN : ∀ {α β} → (α ⊆ β) → Name   α → Name   β
     coerceB : ∀ {α β} → (α ⊆ β) → Binder β → Binder α

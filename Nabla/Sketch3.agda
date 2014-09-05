open import Function.Extensionality
open import Relation.Binary.PropositionalEquality.NP renaming (_≡_ to _==_; _≗_ to _~_)
open import Function

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

data Var {Binder : Type → Type}(w : Type) (b : Binder w) : Type where
  old : w → Var w b
  new : Var w b

module CxtExt (Binder : Type → Set) where 
  infixr 5 _▹_
  _▹_ : (w : Type) (b : Binder w) → Type
  _▹_ = Var

  -- b # v and b' # w
  map▹  : ∀ {v w b} b' -> (v → w) → (v ▹ b) → (w ▹ b')
  map▹ _ f (old x) = old (f x)
  map▹ _ f new = new

record Interface : Set1 where
  -- infix 3 _⊆_
  World = Set -- what I'd call a context of names
  field
    Binder : World → Set     -- type of a binder fresh for w. ('b:Binder w' could be written 'b∉w')
  -- _▹_ : (w : World) → Binder w → World -- extend a world
 
  open CxtExt Binder public

  NablaP : ∀ w → (T : Binder w → Set) → Set
  NablaP = λ w T → Π (Binder w) T

  NablaS : ∀ w → (T : Binder w → Set) → Set
  NablaS = λ w T → Σ (Binder w) T

  ScopeP : World → (T : World → Set) → Set
  ScopeP = λ w T → NablaP w (λ b → T (w ▹ b))

  ScopeS : World → (T : World → Set) → Set
  ScopeS = λ w T → NablaS w (λ b → T (w ▹ b))

  field
    -- Scopes -- Representations of ∇(b∉w). T[b]
    pack   : {w : World} (T : Binder w → Set) → NablaP w T → NablaS w T
    unpack : {w : World} (T : Binder w → Set) → NablaS w T → NablaP w T

  packScope : {w : World} (T : World → Set) → ScopeP w T → ScopeS w T
  packScope {w} T = pack λ b → T (w ▹ b)
  unpackScope : {w : World} (T : World → Set) → ScopeS w T → ScopeP w T
  unpackScope {w} T = unpack λ b → T (w ▹ b)


  unpackPack : ∀ {w : World}  T (g : ScopeP w T) -> g == unpackScope T (packScope T g)
  unpackPack = {!!}

  sndPack : ∀ {w : World}  T (g : ScopeP w T) -> (P : T (w ▹ _) -> Set) ->
             P (g _)  -> P  (snd (packScope T g))
  sndPack = {!!}

    -- Alternative is to use an abstract scope (Nabla) as actual representation; possibly more accurate than both the above.
      -- Nabla : ∀ w → (T : Binder w → Set) → Set
      -- toPi   : ∀ {w T} -> Nabla w T -> Π(Binder w) T
      -- fromPi : ∀ {w T} -> Π(Binder w) T -> Nabla w T 
      -- etc.


    -- no  need for the empty world; we can quantify on all worlds.

    -- refer a specific binder
  name : ∀ {w} → (b : Binder w) → w ▹ b
  name b = new
  
  -- field fresh : ∀ α → Binder α

  exportN : ∀ {α b} → (n : α ▹ b) → (name b == n) ⊎ α
  exportN (old x) = right x
  exportN new = left refl

  exportN-name : ∀ {α} (b : Binder α) → exportN (name b) == left refl
  exportN-name b = refl

  record _⇉_ (α β : World) : Set where
    constructor mk⇉
    field
      wkN : α → β
  open _⇉_ public

  instance
    ⇉-skip :  ∀ {α} {b} → α ⇉ ( α ▹ b )
    ⇉-skip = mk⇉ old

    ⇉-refl : ∀ {w} → w ⇉ w
    ⇉-refl = mk⇉ λ x → x

    {- not sure on how instance arguments
    ⇉-▹ :  ∀ {α β}{b}{{s : α ⇉ β}} → (α ▹ wkB ? b) ⇉ (β ▹ b)
    ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ s x

    OR

    ⇉-▹ :  ∀ {α β}{b}{{s : α ⇉ β}}{{b'}} → (α ▹ b) ⇉ (β ▹ b')
    ⇉-▹ {{mk⇉ s}} = mk⇉ λ x → map▹ s x
    -}

  wkN' : ∀ {α β} {{s : α ⇉ β}} → α → β -- better: subtyping
  wkN' = wkN …

  name' : ∀ {w w'}(b : Binder w) {{s : (w ▹ b) ⇉ w'}} → w'
  name' b = wkN' (name b)

module Example (i : Interface) where
  open Interface i

  data Tm (w : World) : Type where
    var : w -> Tm w
    lam : ScopeS w Tm -> Tm w
    app : Tm w -> Tm w -> Tm w

  lamP : ∀ {w} → ScopeP w Tm -> Tm w
  lamP f = lam (packScope Tm f)
  
  var' : ∀ {w w'}(b : Binder w){{s : (w ▹ b) ⇉ w'}} → Tm w'
  var' b = var (name' b)

  renT : ∀ {α β} → (α → β) → Tm α → Tm β
  renT f (var x)       = var (f x)
  renT f (lam (b , t)) = lamP λ b' → renT (map▹ _ f) t
  renT f (app t u)     = app (renT f t) (renT f u)

  pair= : ∀ {A} {B : A → Type} {p q : Σ A B} (e : fst p == fst q) → tr B e (snd p) == snd q → p == q
  pair= {p = fst , snd} {.fst , snd₁} refl eq = cong (_,_ fst) eq

  lamPS=-fst : ∀ {w} {f : ScopeP w Tm} {g : ScopeS w Tm} → f (fst g) == snd g → lamP f == lam g
  lamPS=-fst f = ap lam (pair= {!!} {!!}) 

  lamPS= : ∀ {w} {f : ScopeP w Tm} {g : ScopeS w Tm} {b} → f b == unpackScope Tm g b → lamP f == lam g
  lamPS= f = {!!} 

  {-
  lamPS= : ∀ {w} {f : ScopeP w Tm} {g : ScopeS w Tm} → (∀ (b : Binder w) → f b == unpack Tm g b) → lamP f == lam g
  lamPS= f = {!!} 
  -}

  lamP= : ∀ {w} {f g : ScopeP w Tm} → (∀ (b : Binder w) → f b == g b) → lamP f == lamP g
  lamP= {w} {f} {g} pf = ap lam (ap (packScope Tm) {!!}) 

  lamP=' : ∀ {w} {f g : ScopeP w Tm} b → f b == g b → lamP f == lamP g
  lamP=' {w} {f} {g} b pf = ap lam (ap (packScope Tm) {!!}) 

  map▹-id : ∀ {α}{f : α → α} (pf : ∀ x → f x == x){b'} t → map▹ b' f t == t
  map▹-id pf (old x) = ap old (pf x)
  map▹-id pf new = refl

  renT-id : ∀ {α}{f : α → α} (pf : ∀ x → f x == x) (t : Tm α) → renT f t == t
  renT-id f (var x) = ap var (f x)
  renT-id f (lam (b' , t)) = lamPS=-fst (renT-id (map▹-id f) t)
  renT-id f (app t t₁) = ap₂ app (renT-id f t) (renT-id f t₁)

  map▹-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ} b0 b1 b2 (h= : f ∘ g ~ h) t
          → map▹ b2 f (map▹ {b = b0} b1 g t) == map▹ b2 h t
  map▹-∘ b0 b1 b2 h= (old x) = ap old (h= x)
  map▹-∘ b0 b1 b2 h= new = refl

  renT-∘ : ∀ {α β γ}{f : β → γ}{g : α → β}{h : α → γ} (h= : f ∘ g ~ h) t
          → renT f (renT g t) == renT h t
  renT-∘ h= (var x) = ap var (h= x)
  renT-∘ {f = f} {g = g} {h = h}  h=  (lam (b , t)) = lamP= λ b' → sndPack Tm (λ b'' → renT (map▹ b'' g) t)
                                                                     (λ tm → renT (map▹ b' f) tm == renT (map▹ b' h) t)
                                                                     (renT-∘ (map▹-∘ _ _ _ h=) t)
  renT-∘ h= (app t u) = {!!}

  wkT : ∀ {α β} {{s : α ⇉ β}} → Tm α → Tm β
  wkT = renT wkN'

  wkT' : ∀ {α β} (s : α ⇉ β) → Tm α → Tm β
  wkT' s = wkT {{s}}

  -- α ⇉ β → α ⇶ β 

  _⇶_ : World → World → Type
  α ⇶ β = α → Tm β

  ext : ∀ {v w b} b' (s : v ⇶ w) → (v ▹ b) ⇶ (w ▹ b')
  ext b' f (old x) = wkT (f x)
  ext b' f new = var new

  substT : ∀ {α β} (s : α ⇶ β) → Tm α → Tm β
  substT s (var x) = s x
  substT s (lam (b , t)) = lamP λ b' → substT (ext b' s) t
  substT s (app t u) = app (substT s t) (substT s u)

  joinT : ∀ {α} → Tm (Tm α) → Tm α
  joinT = substT (λ x → x)

  _∘s_ : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) → α ⇶ γ
  (s ∘s s') x = substT s (s' x)

  {-
  unpack= : ∀ {T : World → Type} {w b b'} {t : T (w ▹ b)} {t' : T (w ▹ b')} → t == t' → unpack {T} (b , t) == unpack {T} (b , t')
  unpack= e = {!!}
-}

  _~ss_ : ∀ {α β} (s s' : α ⇶ β) → Type
  s ~ss s' = ∀ t → substT s t == substT s' t

  -- exportN (wkN i x)

  foo : ∀ {w} s i t → substT (ext {w} {!!} s) (wkT {{i}} t) == wkT {{i}} (substT s t)
  foo s i (var x) = {!!}
  foo s i (lam (b , t)) = {!!}
  foo s i (app t u) = {!!}

  {-
  ext-hom' : ∀ {α β γ} b (s : β ⇶ γ) (s' : α ⇶ β) → (ext ? s ∘s ext {b = b} ? s') ~ ext ? (s ∘s s')
  ext-hom' b s s' (var x) with exportN x
  ext-hom' b s s' (var x) | left x₁ = {!!}
  ext-hom' b s s' (var x) | right x₁ = {!foo s!}
  ext-hom' b s s' (lam (b' , t)) = {!!}
  ext-hom' b s s' (app t u) = {!!}
  ext-hom : ∀ {α β γ} b (s : β ⇶ γ) (s' : α ⇶ β) → (ext s ∘s ext {b = b} s') == ext (s ∘s s')
  ext-hom b s s' = {!!}
-}

  -- ext-hom' b s s' = ap (λ z → substT z t) (ext-hom b s s')
  -- (snd (packScope Tm (λ b'' → renT (map▹ b'' .g) t)))


  {-
  NablaP w T = Π (Binder w) \ b -> T (w ▹ b)
  lamP : ∀ {w} → NablaP w Tm -> Tm w
  lamP f = lam (pack Tm f)
  -}

  _~s_ : {α β : World} (s s' : α ⇶ β) → Type
  s ~s s' = ∀ x → s x == s' x

  ext-var : ∀ {α}{s : α ⇶ α}{b} (s= : s ~s var) → ext b s ~s var
  ext-var s= (old x) = ap wkT (s= x)
  ext-var s= new     = refl

  substT-var : ∀ {α}{s} (s= : s ~s var) (t : Tm α) → substT s t == t
  substT-var s= (var x) = s= x
  substT-var s= (lam (b , t)) = lamPS=-fst (substT-var (ext-var s=) t)
  substT-var s= (app t u) = ap₂ app (substT-var s= t) (substT-var s= u)

  substT-hom : ∀ {α β γ} (s : β ⇶ γ) (s' : α ⇶ β) t → substT s (substT s' t) == substT (s ∘s s') t
  substT-hom s s' (var x) = refl
  substT-hom s s' (lam (b , t)) =
    lamPS=-fst {!substT-hom ? ? t ∙ ?!}
    -- ap lam (pair= refl (substT-hom (ext s) (ext s') t ∙ ext-hom' b s s' t))!}
  substT-hom s s' (app t u) = ap₂ app (substT-hom s s' t) (substT-hom s s' u)

  idTm : ∀ {w} -> Tm w
  idTm = lamP λ x → var (name x)
  
  apTm : ∀ {w} (b : Binder w) -> Tm w
  apTm {w} b = lamP λ x → lamP λ y → app (var' x) (var' y)

  {-
  η : ∀ {w} → Tm w → Tm w
  η t = lamP λ x → app (wkT t) (var' x)
  
  ap' : ∀ {w} -> NablaP w (λ w' → NablaP w' Tm)
  ap' = λ x → λ y → app (var (wkN (⇉-skip y) (name x))) (var (name y))

  {- invalid!
  invalid : ∀ {w} (b : Binder w) → Tm ((w ▹ b) ▹ b)
  invalid = λ b → ap' b b
  -}
  
Ctx = Type
{-
mutual
  data Ctx : Set where
    nil : Ctx
    cons : (c : Ctx) -> Bnd c -> Ctx -- we could do everything with just nats.
-}

Bnd : Ctx -> Set
Bnd _ = One
open CxtExt (λ _ → One)
nil = Zero
cons = _▹_

Idx : Ctx → Set
Idx w = w

here : ∀ {c b} -> Idx (cons c b)
here = new
there : ∀ {c b} -> Idx c -> Idx (cons c b)
there = old
{-
data Idx : Ctx -> Set1 where
  here : ∀ {c b} -> Idx (cons c b)
  there : ∀ {c b} -> Idx c -> Idx (cons c b)

_==i_ : ∀ {α} (x y : Idx α) → Bool
here ==i here = true
here ==i there y = false
there x ==i here = false
there x ==i there y = x ==i y
-}

{-
exportI : ∀ {α b} → (n : Idx (cons α b)) → T (here ==i n) ⊎ (Idx α)
exportI {b = tt} here = left tt
exportI {b = tt} (there n) = right n
-}

{-
exportI : ∀ {α b} → (n : Idx (cons α b)) → (here == n) ⊎ (Idx α)
exportI {b = tt} here = left refl
exportI {b = tt} (there n) = right n
-}

_incl_ : Ctx -> Ctx -> Set
w incl w' = w → w'
done : ∀ {c} -> nil incl c
done ()
skip  : ∀ {v w b} -> v incl w -> v incl (cons w b)
skip i x = old (i x)
take  : ∀ {v w b} -> v incl w -> (cons v b) incl (cons w b)
take = map▹
{-
data _incl_ : Ctx -> Ctx -> Set where
  done : ∀ {c} -> nil incl c
  skip  : ∀ {v w b} -> v incl w -> v incl (cons w b)
  take  : ∀ {v w b} -> v incl w -> (cons v b) incl (cons w b)

wkI : ∀ {v w} -> v incl w -> Idx v -> Idx w
wkI done ()
wkI (skip p) i = there (wkI p i)
wkI (take p) i = here
-}
wkI : ∀ {v w} -> v incl w -> Idx v -> Idx w
wkI x = x

incl-refl : ∀ {w} → w incl w
incl-refl x = x
{-
incl-refl {nil} = done
incl-refl {cons w x} = take incl-refl
-}

incl-cons :  ∀ {α β} b → (s : α incl β) → (cons α b) incl ( cons  β b )
incl-cons b = take

incl-skip :  ∀ {α} b → α incl ( cons  α b )
incl-skip b = skip incl-refl

implem : Interface
implem = record
           { -- World = Ctx
             Binder = Bnd
           -- ; Name = Idx
           -- ; _▹_ = cons
           ; pack = λ T f → tt , f tt
           ; unpack = λ T b x → snd b
           -- ; name = λ b → here
           -- ; _==N_ = _==i_
           -- ; exportN = exportI
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
           ; sucB = λ x → x
           -- ; exportN-name = {!!}
           }
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}
-- -}

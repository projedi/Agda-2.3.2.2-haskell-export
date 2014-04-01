module Vec where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC suc #-}
{-# BUILTIN ZERO zero #-}

_+_ : Nat → Nat → Nat
zero + m = m
(suc n) + m = suc (n + m)

postulate
  Int : Set
  Level : Set
  level-zero : Level
  level-suc : Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO level-zero #-}
{-# BUILTIN LEVELSUC level-suc #-}

data _==_ {l : Level} {A : Set l} (x : A) : A → Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

cong : {A B : Set} {x y : A} (f : A → B) → (x == y) → (f x == f y)
cong f refl = refl

suc-in-+ : (n m : Nat) → (n + suc m) == (suc n + m)
suc-in-+ zero m = refl
suc-in-+ (suc n) m = cong suc (suc-in-+ n m)

data Vec (A : Set) : Nat → Set where
  [] : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)

double-elems : ∀ {A n} → Vec A n → Vec A (n + n)
double-elems [] = []
double-elems {A} {suc n} (x ∷ xs) rewrite cong suc (suc-in-+ n n) with x ∷ (x ∷ double-elems xs)
... | xxs = xxs

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

list-length : ∀ {A} → List A → Nat
list-length [] = zero
list-length (x ∷ xs) = suc (list-length xs)

list-to-vec : {A : Set} (xs : List A) → Vec A (list-length xs)
list-to-vec [] = []
list-to-vec (x ∷ xs) = x ∷ list-to-vec xs

vec-to-list : ∀ {A n} → Vec A n → List A
vec-to-list [] = []
vec-to-list (x ∷ xs) = x ∷ vec-to-list xs

double-list-elems : ∀ {A} → List A → List A
double-list-elems xs = vec-to-list (double-elems (list-to-vec xs))

example-fun-1 : {A : Set} -> ({B : Set} -> List B -> List B) -> List A -> List A
example-fun-1 f xs = f xs

example-fun-2 : {A C : Set} -> ({B : Set} -> List B -> List B) -> List A -> List A
example-fun-2 f xs = f xs

nil : {A : Set} -> List A
nil = []

cons : {A : Set} -> A → List A → List A
cons = _∷_

{-# EXPORT Nat Nat #-}
{-# EXPORT List List #-}
{-# EXPORT nil nil #-}
{-# EXPORT cons cons #-}
{-# EXPORT list-length listLength #-}
{-# EXPORT double-list-elems (+:+) #-}
{-# EXPORT example-fun-1 exampleFun1 #-}
{-# EXPORT example-fun-2 exampleFun2 #-}

record Sigma (A : Set) (B : A -> Set) : Set where
   constructor _,_
   field
      proj1 : A
      proj2 : B proj1
   swap : Sigma (B proj1) (\ _ -> A)
   swap = record { proj1 = proj2 ; proj2 = proj1 }

record Simple (A : Set) : Set where
   constructor simple
   field
      whyamihere : A

{-# EXPORT Simple Simple #-}

vec-map : {A B : Set} {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vec-map f [] = []
vec-map f (x ∷ xs) = f x ∷ vec-map f xs

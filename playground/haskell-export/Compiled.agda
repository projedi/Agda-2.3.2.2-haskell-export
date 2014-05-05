module Compiled where

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

-- TODO: How will it compile dependent types?

-- No data will be generated.
{-# COMPILED_DATA List [] [] (:) #-}

postulate
  Maybe : Set → Set
  nothing : {A : Set} → Maybe A
  just : {A : Set} → A → Maybe A
  maybe : {A B : Set} → B → (A → B) → Maybe A → B

{-# COMPILED_TYPE Maybe Maybe #-}
{-# COMPILED nothing (\_ -> Nothing) #-}
{-# COMPILED just (\_ -> Just) #-}
{-# COMPILED maybe (\_ _ -> maybe) #-}

-- Will generate type a -> [t] -> b
head1 : {A : Set} → List A → Maybe A
head1 nil = nothing
head1 (cons x _) = just x

data Maybe' (A : Set) : Set where
  Nothing : Maybe' A
  Just : A → Maybe' A

{-# COMPILED_DATA Maybe' Maybe Nothing Just #-}

-- Will generate type a -> [t] -> b
head2 : {A : Set} → List A → Maybe' A
head2 nil = Nothing
head2 (cons x _) = Just x

-- Will generate type a1 -> a2 -> Maybe a -> b
f : {A : Set} → List A → Maybe' A → Maybe A
f _ (Just x) = just x
f (cons x _) _ = just x
f _ _ = nothing

-- Will generate type a1 -> [a] -> a2 -> b
g : {A : Set} → List A → Maybe' A → Maybe A
g (cons x _) _ = just x
g _ (Just x) = just x
g _ _ = nothing

-- Will generate type a -> a1 -> b
h : {A : Set} → Maybe A → Maybe' A
h x = maybe Nothing Just x

simpleMap : {A B : Set} → (A → Maybe' B) → List A → List (Maybe B)
simpleMap f nil = nil
simpleMap f (cons x xs) with f x
... | Nothing = cons nothing (simpleMap f xs)
... | (Just y) = cons (just y) (simpleMap f xs)

{-# EXPORT simpleMap simpleMap #-}

maybeMap : {A B : Set} → (A → Maybe' B) → List A → List B
maybeMap f nil = nil
maybeMap f (cons x xs) with f x
... | Nothing = maybeMap f xs
... | (Just y) = cons y (maybeMap f xs)

{-# EXPORT maybeMap maybeMap #-}

hoZipWith : {A B : Set} → ({C : Set} → (A → C) → A → Maybe' C) →
   List (A → B) → List A → List B
hoZipWith _ nil _ = nil
hoZipWith _ _ nil = nil
hoZipWith g (cons f fs) (cons x xs) with g f x
... | Nothing = hoZipWith g fs xs
... | Just y = cons y (hoZipWith g fs xs)

{-# EXPORT hoZipWith hoZipWith #-}

-- Therefore:

-- COMPILED functions should be forbidden to be exported
-- COMPILED_TYPE should be forbidden to be exported.
-- These two are automagical because postulates are not exportable...
-- COMPILED_DATA should be forbidden to be exported

-- COMPILED_TYPE and COMPILED_DATA is not possible because
-- COMPILED_TYPE only works on postulates and COMPILED_DATA
-- on data(not even records are accepted)

-- When in a type there is COMPILED_TYPE or COMPILED_DATA
-- put them in a type and then just do casts.

{-
{-# EXPORT List List #-}
{-# EXPORT Maybe Maybe1 #-}
-}

{-# EXPORT f f #-}
{-# EXPORT g g #-}
{-# EXPORT h h #-}

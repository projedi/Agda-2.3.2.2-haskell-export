module HOKinds where

data T : Set where

data HOKinds (A : (Set → Set) → Set → Set) : (Set → Set) → Set where
  cons1 : HOKinds A (λ _ → T)

{-# EXPORT HOKinds HOKinds #-}

hoid : {M : Set → Set} {A B : Set} → M A → (M A → M B) → M B
hoid x f = f x

{-# EXPORT hoid hoid #-}

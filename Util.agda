module Util where

open import Data.Product
open import Agda.Builtin.Equality

-- this is called the inspect idiom, in the Agda stdlib
keep : ∀{ℓ}{A : Set ℓ} → (x : A) → Σ A (λ y → x ≡ y)
keep {ℓ} {A} x = ( x , refl )



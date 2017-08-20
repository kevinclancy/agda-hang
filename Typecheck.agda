
module Typecheck where

open import Function using (_∘_; _$_)

import ast as S
open import ast using (τ ; c)

-- The functions exported by these modules are use everywhere, so we import everything
open import Size -- Size , Size< , etc
open import Data.Product -- × , proj₁ , proj₂ , Σ , etc.
open import Relation.Binary.PropositionalEquality as PE -- ≡, sym, etc.
open import Relation.Binary
open import Data.Vec as V hiding (_++_ ; [_])
open import Data.Fin hiding (_+_ ; _≤_ ; _<_)
open import Data.Nat.Properties.Simple as NPS 
open import Data.Integer as Z hiding (suc ; _+_)
open import Data.Bool as B hiding (T)
open import Util

-- these modules have names 
open import Data.Nat as N
open import Algebra as A
open import Data.Nat.Properties as NP

open import Data.Vec.All using (All₂)

Ξ : ℕ → Set 
Ξ = Vec S.q

data Γ : (n : ℕ) → Set
data Γ' {m : ℕ} (Γ₀ : Γ m) : (n : ℕ) → Set 
data Ω {m : ℕ} (Γ₀ : Γ m) : (n : ℕ) → Set
data Φ {l m : ℕ} (Γ₀ : Γ l) (Ω₀ : Ω Γ₀ m) : (n : ℕ) → Set

data PrefixΓ : {m n : ℕ} → (Γ₀ : Γ m) → (Γ₁ : Γ n) → Set
data PrefixΦ : {l m n k : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} (Φ₀ : Φ Γ₀ Ω₀ n) (Φ₁ : Φ Γ₀ Ω₀ k) → Set

data T {i : Size} {n : ℕ} (Γ₀ : Γ n) : Set
data  Ṫ {i : Size} {l m n : ℕ} (Γ₀ : Γ l) (Ω₀ : Ω Γ₀ m) (Φ₀ : Φ Γ₀ Ω₀ n) : Set
data t {i : Size} {n : ℕ} (Γ₀ : Γ n) : {m : ℕ} {Γ₁ : Γ m} {p : PrefixΓ Γ₁ Γ₀} → (T₀ : T Γ₁) → Set
data ṫ {i : Size} {l m n : ℕ} (Γ₀ : Γ l) (Ω₀ : Ω Γ₀ m) (Φ₀ : Φ Γ₀ Ω₀ n) : 
       {k : ℕ} {Φ₁ : Φ Γ₀ Ω₀ k} {p : PrefixΦ Φ₁ Φ₀} (Ṫ₀ : Ṫ Γ₀ Ω₀ Φ₁) → Set

natT : {i : Size} {n : ℕ} {Γ₀ : Γ n} → T {↑ ↑ ↑ i} Γ₀
fixMetricT : {i : Size} {n : ℕ} {Γ₀ : Γ n} → (t₀ : t Γ₀ natT) → T {i} Γ₀
boolT : {i : Size} {n : ℕ} {Γ₀ : Γ n} → T {↑ i} Γ₀ 

boolṪ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} → Ṫ {i} Γ₀ Ω₀ Φ₀
natṪ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} → Ṫ {i} Γ₀ Ω₀ Φ₀

data Γ where
  · : Γ 0
  _,Γ⟨_⟩_ : {n : ℕ} → (prev : Γ n) → (i : Size) → (T {i} prev) → Γ (suc n)

data Ω {m : ℕ} (Γ₀ : Γ m) where
  · : Ω Γ₀ 0
  _,Ω⟨_⟩_ : {n : ℕ} → (prev : Ω Γ₀ n) → (i : Size) → τ × (t {i} Γ₀ boolT) → Ω Γ₀ (suc n)

data Φ {l m : ℕ} (Γ₀ : Γ l) (Ω₀ : Ω Γ₀ m) where
  · : Φ Γ₀ Ω₀ 0
  _,Φ⟨_⟩_ : {n : ℕ} → (prev : Φ Γ₀ Ω₀ n) → (i : Size) → (Ṫ {i} Γ₀ Ω₀ prev) → Φ Γ₀ Ω₀ (suc n)

infixl 10 _,Γ⟨_⟩_
infixl 10 _,Ω⟨_⟩_
infixl 10 _,Φ⟨_⟩_ 

constantType : {i : Size} → S.c → T {i} ·

-- Returns the type of the specified primitive
primType : {i : Size} → S.SfPrimitive → T {i} ·
primType p = {!!}

_Γ+τ_ : {len : ℕ} → Γ len → S.τ → Γ (suc len)
_Φ+τ_ : {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} → Φ Γ₀ Ω₀ n → S.τ → Φ Γ₀ Ω₀ (suc n)

infixl 10 _Γ+τ_
infixl 10 _Φ+τ_

-- weakenT : ∀ {n : ℕ} {Γ₀ : Γ n} {T₀ : T Γ₀}
makeAmbientEnv : ∀ {i : Size} {l m : ℕ} {Γ₀ : Γ l} → Vec (Σ S.τ (λ τ₀ → t {i} (Γ₀ Γ+τ τ₀) boolT)) m → Ω Γ₀ m  
makeSelectorEnv : ∀ {i : Size} {l m : ℕ} {Γ₀ : Γ l} → (formals : Vec (Σ S.τ (λ τ₀ → t {i} (Γ₀ Γ+τ τ₀) boolT)) m) → 
                     Φ {l} {m} Γ₀ (makeAmbientEnv formals) m

_++Γ_ : {n m : ℕ} → (Γ₀ : Γ n) → Γ' Γ₀ m → Γ (n + m)
_++Φ_ : {j k l n : ℕ} {Γ₀ : Γ j} {Ω₀ : Ω Γ₀ k} → Φ Γ₀ Ω₀ l → Φ Γ₀ Ω₀ n → Φ Γ₀ Ω₀ (l + n) 

infixl 10 _++Γ_
infixl 10 _++Φ_

⌊_⌋Γ : ∀ {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} → (Φ₀ : Φ Γ₀ Ω₀ n) → (Γ' Γ₀ n) 
⌊_⌋T : ∀ {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} → (Ṫ {i} Γ₀ Ω₀ Φ₀) → (T {i} (Γ₀ ++Γ ⌊ Φ₀ ⌋Γ))

ṪLift : ∀ {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ l} {Φ₀ : Φ Γ₀ Ω₀ m} → (T₀ : T (Γ₀ ++Γ ⌊ Φ₀ ⌋Γ)) → Ṫ Γ₀ Ω₀ Φ₀
-- ṫLift : ∀ {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} → 
--          (Ṫ₀ : Ṫ Γ₀ Ω₀ Φ₀) → (t₀ : t (Γ₀ ++Γ ⌊ Φ₀ ⌋Γ) ⌊ Ṫ₀ ⌋T) → 
--          ṫ Γ₀ Ω₀ Φ₀


t↑∞ : {i : Size} {n : ℕ} {Γ₀ : Γ n} {T₀ : T Γ₀} (t₀ : t {i} Γ₀ T₀) → t {∞} Γ₀ T₀

T↑∞ : {i : Size} {n : ℕ} {Γ₀ : Γ n} → (T {i} Γ₀) → (T {∞} Γ₀) 

ṫ↑∞ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} {Ṫ₀ : Ṫ Γ₀ Ω₀ Φ₀} → 
      (ṫ₀ : ṫ {i} Γ₀ Ω₀ Φ₀ Ṫ₀) → (ṫ {∞} Γ₀ Ω₀ Φ₀ Ṫ₀)

Ṫ↑∞ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n}  → (Ṫ {i} Γ₀ Ω₀ Φ₀) → (Ṫ {∞} Γ₀ Ω₀ Φ₀)

data Γ' {m : ℕ} (Γ₀ : Γ m) where
  · : Γ' Γ₀ 0
  _,Γ'〈_〉_ : {i : Size} {n : ℕ} → (prev : Γ' Γ₀ n) → T {i} (Γ₀ ++Γ prev) → Γ' Γ₀ (suc n)  

-- lookupΓ-lemma3 : ∀ (n : ℕ) → (lookupInd : ℕ) → (p : lookupInd N.< n) → (n ∸ (lookupInd + 1) + lookupInd) ≡ n ∸ 1

-- proof j ≤ (succ i) + j
{-
  hereΓ : {i j : ℕ} → (prevΓ : Γ i) → (T₀ : T prevΓ) → (afterΓ : Γ' (prevΓ , T₀) j) → 
          LookUpΓ {n} (fromℕ≤" j) ((prevΓ , T₀) ++Γ afterΓ) 
-}

-- lookupΓ-lemma3 : ∀ {n m} → (Γ₀ : Γ n) → (T₀ : T Γ₀) → (Γ₁ : Γ' (Γ₀ ,Γ T₀) m) → (T₁ : T ((Γ₀ ,Γ T₀) ++Γ Γ₁)) → ( (Γ₀ ,Γ T₀) ++Γ (Γ₁ ,Γ' T₁) ≡  ( ((Γ₀ ,Γ T₀) ++Γ Γ₁) ,Γ T₁ ) )  
-- lookupΓ-lemma3 Γ₀ T₀ Γ₁ T₁ = ?

{-
lookupΓ-lemma3 : ∀ {n lookupInd} → (Γ₀ : Γ (n ∸ (lookupInd + 1))) → (T₀ : T Γ₀) → 
                 (Γ₁ : Γ' (Γ₀ ,Γ T₀) lookupInd) → (T₁ : T ((Γ₀ ,Γ T₀) ++Γ Γ₁)) → ( (Γ₀ ,Γ T₀) ++Γ (Γ₁ ,Γ' T₁) ≡  ( ((Γ₀ ,Γ T₀) ++Γ Γ₁) ,Γ T₁ ) )

lookupΓ-lemma3 Γ₀ T₀ Γ₁ T₁ = ?
-}


-- proof that one environment is a prefix of another
data PrefixΓ where
  prefixΓ-Refl : {m : ℕ} → (Γ₀ : Γ m) → PrefixΓ Γ₀ Γ₀
  prefixΓ-Step : {j : Size} {m n : ℕ} → (Γ₀ : Γ m) → (T₀ : T {j} Γ₀) → (Γ₁ : Γ n) → 
                 (p : PrefixΓ (Γ₀ ,Γ⟨ j ⟩ T₀) Γ₁) → (PrefixΓ Γ₀ Γ₁)

-- PrefixΦ Φ₀ Φ₁ proves that Φ₀ is a prefix of Φ₁ 
data PrefixΦ where
  prefixΦ-Refl : {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} → (Φ₀ : Φ Γ₀ Ω₀ m) → PrefixΦ Φ₀ Φ₀
  prefixΦ-Step : {j : Size} {l m n k : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} → 
                 (Φ₀ : Φ Γ₀ Ω₀ n) → 
                 (Ṫ₀ : Ṫ {j} Γ₀ Ω₀ Φ₀) → 
                 (Φ₁ : Φ Γ₀ Ω₀ k) → 
                 (p : PrefixΦ (Φ₀ ,Φ⟨ j ⟩ Ṫ₀) Φ₁) → 
                 (PrefixΦ Φ₀ Φ₁)

lookupΓ : {n : ℕ} → (Γ₀ : Γ n) → Fin n → T {∞} Γ₀ 


-- ****** For now we use only well-formed ast's, meaning that qualifier maps match their enclosing
--        ambient environments, as do the domains of ambient maps, and also that the bodies of embedded sfuns are 
--        wellformed. Well-formedness is weaker than
--        well-typedness; a programmer may write a program which is not well-formed, but it will 
--        be rejected by the type checker. Well-formedness is preserved by single-step reduction. We make 
--        no attempt to implement operational semantics (substitution and reduction) for non-well-formed syntax.
data T {i : Size} {n : ℕ} (Γ₀ : Γ n) where
  -- τ{t}
  RefBase : {j : Size< i} → (τ : τ) → (tPred : t {j} (Γ₀ Γ+τ τ) boolT) → T {i} Γ₀
  -- (x : A, ...) ⇒ A[Ξ]{t}
  SFun : {j k : Size< i} → 
         {numFormals : ℕ} → 
         (formals : Vec (Σ S.τ (λ τ₀ → t {j} (Γ₀ Γ+τ τ₀) boolT)) numFormals) → 
         (τResult : τ) → 
         (Ξ : Ξ numFormals) → 
         (tPred : t {k} ( Γ₀ ++Γ ⌊ makeSelectorEnv formals ⌋Γ Γ+τ τResult) boolT) → 
         T {i} Γ₀
  -- (x : T) → T
  Fun : {j k : Size< i} → (TFormal : T {j} Γ₀) → (TResult : T {k} (Γ₀ ,Γ⟨ j ⟩ TFormal)) → T {i} Γ₀
  -- ⟨x < t⟩ T
  Fix  : {j : Size< i} → 
         (tCurrMetric : t {j} Γ₀ natT) → 
         (TBody : T {j} (Γ₀ ,Γ⟨ ∞ ⟩ (fixMetricT $ t↑∞ tCurrMetric)))
         → T {i} Γ₀
data Ṫ {i : Size} {l m n : ℕ} (Γ₀ : Γ l) (Ω₀ : Ω Γ₀ m) (Φ₀ : Φ Γ₀ Ω₀ n) where 
  -- τ{ṫ}
  RefBase     : {j : Size< i} → (τ₀ : τ) → (ṫPred : ṫ {j} Γ₀ Ω₀ (Φ₀ Φ+τ τ₀) boolṪ) → Ṫ {i} Γ₀ Ω₀ Φ₀
  -- τ[Ξ]{ṫ}
  QualRefBase : {j : Size< i} → (τ₀ : τ) → (Ξ : Ξ m) → (tPred : t {j} (Γ₀ ++Γ ⌊ Φ₀ ⌋Γ Γ+τ τ₀) boolT) → Ṫ {i} Γ₀ Ω₀ Φ₀
  -- (x : A, ...) ⇒ A[Ξ]{t}
  -- note that the third component of each formal is actually a terminal term
  -- statically, sfuns cannot occur nested, and so the predicate is well-typed under Γ₀ ++ ⌊ formals ⌋Γ 
  SFun : {j : Size< i} {arity : ℕ} → 
         (formals : Vec (Σ τ (λ τ₀ → t {j} (Γ₀ Γ+τ τ₀) boolT)) arity) → 
         (τResult : τ) → 
         (Ξ : Ξ arity) → 
         (tPred : t {j} ( Γ₀ ++Γ ⌊ makeSelectorEnv formals ⌋Γ ) boolT) → Ṫ {i} Γ₀ Ω₀ Φ₀
  -- (x : Ṫ) → Ṫ
  -- ugly error Fun  : {j : Size< i} → (ṪFormal : Ṫ {j} Γ₀ Ω₀ Φ₀) → (ṪResult : Ṫ {j} Γ₀ Ω₀ (Φ₀ , ṪFormal)) → Ṫ {i} Γ₀ Ω₀ Φ₀
  Fun  : {j k : Size< i} → (ṪFormal : Ṫ {j} Γ₀ Ω₀ Φ₀) → 
         (ṪResult : Ṫ {k} Γ₀ Ω₀ (Φ₀ ,Φ⟨ j ⟩ ṪFormal)) → Ṫ {i} {l} {m} {n} Γ₀ Ω₀ Φ₀
  -- ⟨x < ṫ⟩ Ṫ
  Fix  : {j k : Size< i} → (ṫCurrMetric : ṫ {j} Γ₀ Ω₀ Φ₀ natṪ) → (ṪBody : Ṫ {j} Γ₀ Ω₀ (Φ₀ ,Φ⟨ k ⟩ natṪ)) → Ṫ {i} Γ₀ Ω₀ Φ₀

-- Proof that U is a subtype of S 
data _<:_ {i j k : Size} {n : ℕ} {Γ₀ : Γ n } (U : T {j} Γ₀) (S : T {k} Γ₀) : Set where
  


-- data t {i : Size} {n : ℕ} (Γ₀ : Γ n) : {m : ℕ} {Γ₁ : Γ m} {p : PrefixΓ Γ₁ Γ₀} → (T₀ : T Γ₁1) → Set
data t {i : Size} {n : ℕ} (Γ₀ : Γ n) where 
  Constant : (c₀ : c) → t {i} Γ₀ {!!} -- (constantType c₀)
  SfConstant : (prim : S.SfPrimitive) → t {i} Γ₀ (primType prim)
  Var : (m : Fin n) → t {i} Γ₀ (lookupΓ Γ₀ m)
  -- (λ (x : T) t)
  -- Terminal function with one argument named x of type T, with body t
  Fun : {j k l : Size< i} → (TFormal : T {j} Γ₀) → (TResult : T {k} (Γ₀ ,Γ⟨ j ⟩ TFormal) ) → 
        (tBody : t {k} (Γ₀ ,Γ⟨ j ⟩ TFormal) (T↑∞ TResult)) → 
        t {i} {_} Γ₀ (Fun TFormal TResult)
  -- (fix t x S y s)
  -- A recursive term abstraction, where t is the termination metric, x is a variable referring to the "next" termination
  -- metric, S is the type of the body of the recursive term, y is a self-reference for the recursive term,
  -- and s is the recursive term itself
  Fix : {j k : Size< i} → 
        (tCurrMetric : t {j} Γ₀ natT) → 
        (TBody : T {k} (Γ₀ ,Γ⟨ _ ⟩ (fixMetricT $ t↑∞ tCurrMetric))) → 
        (tBody : t {j} 
                   ((Γ₀ ,Γ⟨ ∞ ⟩ (fixMetricT $ t↑∞ tCurrMetric)) ,Γ⟨ k ⟩ TBody) 
                   {_} 
                   {(Γ₀ ,Γ⟨ _ ⟩ (fixMetricT $ t↑∞ tCurrMetric))}
                   {prefixΓ-Step (Γ₀ ,Γ⟨ _ ⟩ (fixMetricT $ t↑∞ tCurrMetric)) 
                                 TBody
                                 ((Γ₀ ,Γ⟨ ∞ ⟩ (fixMetricT $ t↑∞ tCurrMetric)) ,Γ⟨ k ⟩ TBody)
                                 (prefixΓ-Refl ((Γ₀ ,Γ⟨ ∞ ⟩ (fixMetricT $ t↑∞ tCurrMetric)) ,Γ⟨ k ⟩ TBody))} 
                   (T↑∞ TBody)) → 
        t {i} Γ₀ (Fix (t↑∞ tCurrMetric) (T↑∞ TBody))
  -- (λλ (x : B ...) ṫ)
  SFun : {j k : Size< i} {arity : ℕ} → 
         (formals : Vec (Σ τ (λ τ₀ → t {j} (Γ₀ Γ+τ τ₀) boolT)) arity) → 
         (τResult : τ) →
         (Ξ₀ : Ξ arity) → 
         (tPred : t {k} (Γ₀ ++Γ ⌊ makeSelectorEnv formals ⌋Γ Γ+τ τResult) boolT) →
         (ṫBody : ṫ {j} Γ₀ (makeAmbientEnv formals) (makeSelectorEnv formals) (QualRefBase τResult Ξ₀ tPred)) → 
         t {i} Γ₀ (SFun {∞} formals τResult Ξ₀ tPred) 
  -- t y
  -- Standard ANF function application
  App : {j k l : Size< i} → (TFormal : T {j} Γ₀) → (TResult : T {k} (Γ₀ ,Γ⟨ j ⟩ TFormal)) → 
        (tFun : t {l} Γ₀ (Fun TFormal TResult)) → 
        (arg : Fin n) → 
        (TActual : T Γ₀) → 
        (p : TActual <: TFormal) →  
        (q : lookupΓ Γ₀ arg ≡ TActual) ->
        --TODO BELOW: need to substitute arg for 0 in TResult
        t {i} Γ₀ (T↑∞ TResult)  
  -- t [ y_1 y_2 ... y_n ]
  -- SFun application
  SApp : {j : Size< i} {arity : ℕ} {formals : Vec (Σ τ (λ τ₀ → (t (Γ₀ Γ+τ τ₀) boolT))) arity}
         {τResult : τ} {Ξ₀ : Ξ arity} {tPred : (t (Γ₀ ++Γ ⌊ makeSelectorEnv formals ⌋Γ Γ+τ τResult) boolT)} → 
         (tFun : t {j} Γ₀ (SFun {∞} formals τResult Ξ₀ tPred)) → 
         -- (args : Vec (Σ (Fin n × T Γ₀) (λ k,T₀ → lookupΓ Γ₀ (proj₁ k,T₀) ≡ (proj₂ k,T₀))) arity) → 
         (args : Vec (Fin n) arity) →
         (TArgs : Vec (T Γ₀) arity) →
         (p : All₂ (λ k → λ T₀ → lookupΓ Γ₀ k ≡ T₀) args TArgs) →
         (q : All₂ (λ τ,tPred → λ TArg → TArg <: (RefBase (proj₁ τ,tPred) (proj₂ τ,tPred))) formals TArgs) → 
         -- Todo: perform substitutions into tPred
         t {i} Γ₀ (RefBase τResult tPred)
  -- t ⟨s⟩
  -- fixpoint application, where t is a fixpoint abstraction and s is its next termination metric
{-
  FixApp : {j : Size< i} → 
           (tCurrMetric : t {j} Γ₀ natT) →
           (TBody : T {j} (Γ₀ ,Γ⟨ ∞ ⟩ (fixMetricT $ t↑∞ tCurrMetric))) →
           (tFix : t {j} Γ₀ (Fix tCurrMetric TBody)) → 
           (tNextMetric : t {j} Γ₀ (fixMetricT $ t↑∞ tCurrMetric)) → 
           -- we need to do a substitution here to fix this error
           t {i} Γ₀ (t↑∞ TBody)
-}
  -- if s then t else u
  -- An if expression, s is the condition, t is the then clause, and u is the else clause
  IfThenElse : {j k l m : Size< i} →
               (TBranch : T {j} Γ₀) 
               (tCond : t {k} Γ₀ boolT) → 
               (tThen : t {l} Γ₀ (T↑∞ TBranch)) → 
               (tElse : t {m} Γ₀ (T↑∞ TBranch)) → 
               t {i} Γ₀ (T↑∞ TBranch)
  -- let x = s in t
  Let : {j k l m : Size< i} →
        (TBind : T {j} Γ₀) →
        (TScope : T {k} Γ₀) →
        (tBind : t {k} Γ₀ (T↑∞ TBind)) → 
        (tScope : t {l} (Γ₀ ,Γ⟨ j ⟩ TBind) (T↑∞ TScope)) → 
        t {i} Γ₀ (T↑∞ TScope)

data ṫ {i : Size} {l m n : ℕ} (Γ₀ : Γ l) (Ω₀ : Ω m) (Φ₀ : Φ n) where
  {-
  Constant : (c : c) → ṫ {i}
  Var : (n : ℕ) → ṫ {i}
  -- 〔... ω ↦ c_ω ...〕
  -- ambient maps track the input/output relation between the valuations of the enclosing sfun 
  -- and a constant at a specific location in the program
  -- AmbientMap : (m : (List c) → Maybe c) → ṫ {i}.  *** Syntax cannot contain ambient maps. well-formed terms will, however.
  
  -- (λ (x : T) t)
  -- Terminal function with one argument named x of type T, with body t
  Fun : {j : Size< i} → (ṪFormal : Ṫ {j}) → (ṫBody : ṫ {j}) → ṫ {i} 
  -- (fix t x S y s)
  -- A recursive term abstraction, where t is the termination metric, x is a variable referring to the "next" termination
  -- metric, S is the type of the body of the recursive term, y is a self-reference for the recursive term,
  -- and s is the recursive term itself
  Fix : {j : Size< i} → (ṫCurrMetric : ṫ {j}) → (ṪBody : Ṫ {j})  → (ṫBody : ṫ {j}) → ṫ {i}
  -- (λλ (x : B ...) ṫ)
  -- note that the third component of each formal is actually a terminal term
  SFun : {j : Size< i} {arity : ℕ} → (formals : Vec (τ × ṫ {j}) arity) → (ṫBody : ṫ {j}) → ṫ {i}
  -- ṫ ṡ
  -- Standard function application
  App : {j : Size< i} → (ṫFun : ṫ {j}) → (ṫArg : ṫ {j}) → ṫ {i}
  -- ṫ [ ṡ_1 ṡ_2 ... ṡ_n ]
  -- SFun application
  SApp : {j : Size< i} {arity : ℕ} → (ṫFun : ṫ {j}) → (ṫArgs : Vec (ṫ {j}) arity) → ṫ {i}
  -- ṫ ⟨ṡ⟩
  -- fixpoint application, where ṫ is a fixpoint abstraction and ṡ is its next termination metric
  FixApp : {j : Size< i} → (ṫFix : ṫ {j}) → (ṫNextMetric : ṫ {j}) → ṫ {i}
  -- if ṫ₀ then ṫ₁ else ṫ₂
  -- An if expression, ṫ_0 is the condition, ṫ₁ is the then clause, and ṫ₂ is the else clause
  IfThenElse : {j : Size< i} → (ṫCond : ṫ {j}) → (ṫThen : ṫ {j}) → (ṫElse : ṫ {j}) → ṫ {i} 
  -- let x = ṡ in ṫ
  Let : {j : Size< i} → (ṫBind : ṫ {j}) → (ṫScope : ṫ {j}) → ṫ {i}
-}

{-
⌈_⇡_⌉t : ∀ {n m : ℕ} {Γ₀ : Γ n} {T₀ : T Γ₀} → (t₀ : t Γ T₀) → (Ω₀ : Ω m) → (ṫ Γ₀ Ω₀ ·)
⌈ t ⇡ Ω ⌉t = ?  
-}

-- t↑∞ : {i : Size} {n : ℕ} {Γ₀ : Γ n} {T₀ : T Γ₀} (t₀ : t {i} Γ₀ T₀) → t {∞} Γ₀ T₀
t↑∞ {i} {n} {Γ₀} T₀ = ?

-- forget : {i : Size} {n : ℕ} {Γ₀ : Γ n} → (T {i} Γ₀) → (T {∞} Γ₀) 
T↑∞ {i} {n} {Γ₀} (RefBase {_} τ₁ tPred) =  RefBase {∞} τ₁ tPred
T↑∞ {i} {n} {Γ₀} (SFun {_} {numFormals} formals τResult Ξ₁ tPred) =  SFun {∞} {_} {_} {_} {numFormals} formals τResult Ξ₁ tPred
T↑∞ {i} {n} {Γ₀} (Fun {j} TFormal TResult) = Fun {∞} {_} {_} {_} TFormal TResult
T↑∞ {i} {n} {Γ₀} (Fix {j} tCurrMetric T₁) = Fix {∞} {_} {_} {_} tCurrMetric T₁


-- ṫ↑∞ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Γ₀ m} {Φ₀ : Γ₀ Ω₀ n} {Ṫ₀ : Ṫ Γ₀ Ω₀ Φ₀} → 
--      (t₀ : t {i} Γ₀ Ω₀ Φ₀ Ṫ₀) → (t {∞} Γ₀ Ω₀ Φ₀ Ṫ₀)
ṫ↑∞ t₀ = ?

-- Ṫ↑∞ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Γ₀ m} {Φ₀ : Γ₀ Ω₀ n}  → (Ṫ {i} Γ₀ Ω₀ Φ₀) → (Ṫ {∞} Γ₀ Ω₀ Φ₀)
Ṫ↑∞ t₀ = ?

-- makeAmbientEnv : ∀ {l m : ℕ} {Γ₀ : Γ l} → Vec (S.τ × t {j} Γ₀ boolT) m → Ω m  
makeAmbientEnv formals = {!!}

-- makeSelectorEnv : ∀ {l m : ℕ} {Γ₀ : Γ l} → (formals : Vec (S.τ × t {j} Γ₀ boolT) m) → 
--                     Φ {l} {m} {Γ₀} {makeAmbientEnv formals} m
makeSelectorEnv [] = ·
makeSelectorEnv ((τ , t) ∷ Ω₀) = {!!} -- (makeSelectorEnv Ω₀ , QualRefBase τ ? ⌈ t ⇡ Ω ⌉t) 

-- _+τ_ : {len : ℕ} → Γ len → S.τ → Γ (suc len)
Γ₀ Γ+τ τ₀ = {!!} -- (Γ₀ , RefBase τ₀ boolT)          

-- _+τ_ : {len : ℕ} → Φ len → S.τ → Φ (suc len)
Φ₀ Φ+τ τ₀ = {!!} -- (Φ₀ , RefBase τ₀ boolT)

-- boolT : {i : Size} {n : ℕ} → {Γ₀ : Γ n} → T {i} Γ₀
boolT {i} = RefBase {↑ i} S.τBool (Constant {i} (S.cBool true)) 

-- natT : {i : Size} {n : ℕ} → {Γ₀ : Γ n} → T {i} Γ₀
natT {i} = RefBase {↑ ↑ ↑ i} S.τInt 
                            (Let {↑ ↑ i} intT
                               boolT
                               (Constant {↑ i} (S.cInt $ + 0))
                               (SApp {↑ i} (SfConstant {i} S.SfLess) 
                                           ((fromℕ 0) ∷ (fromℕ 1) ∷ [])
                                           (intT ∷ intT ∷ [])
                                           (refl ∷ refl ∷ [])
                                           ?))
     where
       intT = (RefBase S.τInt (Constant $ S.cBool true))

-- fixMetricT : {i : Size} {n : ℕ} {Γ₀ : Γ n} → (tPrevMetric : t) → T {i} Γ₀
fixMetricT tPrevMetric = RefBase S.τInt (SApp (S.SfConstant S.SfAnd) 
                                     [ (SApp (S.SfConstant S.SfLess) 
                                             [ (Constant (S.cInt 0)) , (Var 0) ])
                                       (SApp (S.SfConstant S.SfLess)
                                             [ (Var 0) , tPrevMetric ]) ])

-- boolṪ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} → Ṫ {i} Γ₀ Ω₀ Φ₀
boolṪ = {!!} -- RefBase S.τBool (Constant (S.cBool true))

-- natṪ : {i : Size} {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Φ Γ₀ Ω₀ n} → Ṫ {i} Γ₀ Ω₀ Φ₀
-- for now it is unqualified... allowing qualifiers would require a revised lifted operational semantics 
-- (reduction sequences index by ordinals?)
natṪ = {!!} -- RefBase S.τInt (SApp (S.SfConstant S.SfLess) [ (Constant (S.cInt 0)) , (Var 0) ])

-- constantType : {i : Size} → S.c → T {i} · 
constantType c = {!!}

-- _++_ : {n m : ℕ} → Γ n → Γ m → Γ (n + m)
a ++Γ b = {!!}

-- _++Φ_ : {j k l n : ℕ} {Γ₀ : Γ j} {Ω₀ : Ω k} → Φ Γ₀ Ω₀ l → Φ Γ₀ Ω₀ n → Φ Γ₀ Ω₀ (l + n) 
a ++Φ b = {!!}

⌊ Ṫ ⌋T = {!!}

⌊ Φ ⌋Γ = {!!}


-- ⌈_⌉Φ : ∀ {m n : ℕ} → (Γ₀ : Γ m) → (Ω₀ : Ω Γ₀ n) → (Φ · Ω₀ m)
⌈_⌉Φ = ?

-- ṪLift : ∀ {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ l} {Φ₀ : Γ₀ Ω₀ m} → (T₀ : T Γ₀ ++Γ ⌊ Φ ⌋Γ) → Ṫ Γ₀ Ω₀ Φ₀
ṪLift T₀ = ?

-- ṫLift : ∀ {l m n : ℕ} {Γ₀ : Γ l} {Ω₀ : Ω Γ₀ m} {Φ₀ : Γ₀ Ω₀ n} → (t₀ : t Γ₀ ++Γ ⌊ Φ ⌋Γ) → ṫ Γ₀ Ω₀ Φ₀
-- ṫLift t₀ = ? 

-- I need weakening: if I'm well-formed or well-typed under context, I'm well-formed under extension of that context
weaken1 : ∀  {i j : Size} {n : ℕ} → (Γ₀ : Γ n) → (T₀ : T {i} Γ₀) → (T₁ : T {j} Γ₀) → T {∞} (Γ₀ ,Γ⟨ j ⟩ T₁)
weaken1 T₀ = {!!}

weakenBy : ∀ {i : Size} {n m : ℕ} → (Γ₀ : Γ n) → (T₀ : T {i} Γ₀) → (Γ₁ : Γ m) → (p : PrefixΓ Γ₀ Γ₁) → T {∞} Γ₁
weakenBy Γ₀ T₀ .Γ₀ (prefixΓ-Refl .Γ₀) = T↑∞ T₀
weakenBy Γ₀ T₀ Γ₁ (prefixΓ-Step {i} .Γ₀ T₁ .Γ₁ p) = weakenBy (Γ₀ ,Γ⟨ i ⟩ T₁) (weaken1 Γ₀ T₀ T₁) Γ₁ p


lookupΓ {n} Γ₀ l = (lookupΓ-aux n Γ₀ (prefixΓ-Refl Γ₀) (toℕ l) (bounded l))
  where open import Data.Fin.Properties
        lookupΓ-aux : (n : ℕ) → (Γ₁ : Γ n) → (p : PrefixΓ Γ₁ Γ₀) → (lookupInd : ℕ) → 
                      (q : lookupInd N.< n) → T {∞} Γ₀  
        lookupΓ-aux (suc _) (Γ₁' ,Γ⟨ _ ⟩ T₁) p 0 (s≤s z≤n) = weakenBy Γ₁' T₁ Γ₀ (prefixΓ-Step Γ₁' T₁ Γ₀ p)
        lookupΓ-aux (suc n') (Γ₁ ,Γ⟨ _ ⟩ T₁) p (suc lookupInd') (s≤s (s≤s q)) = 
          (lookupΓ-aux n' Γ₁ (prefixΓ-Step Γ₁ T₁ Γ₀ {!!}) lookupInd' (s≤s q))
        lookupΓ-aux zero · p lookupInd ()  



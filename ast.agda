module ast where

open import Data.String hiding (_==_)
open import Data.List as L
open import Data.Vec as V
open import Data.Product
open import Data.Integer
open import Data.Nat
open import Util
open import Data.Maybe
open import Data.Bool hiding (T)
open import Size
open import Function using (_∘_ ; _$_)
-- Variables .... not sure this representation is going to work
-- var : Set
-- var = String

-- Base-level types (\tau)
-- These types describe pieces of data. They do *not* describe functions.
data τ : Set where
  τInt  : τ
  τBool : τ

-- lifted term
data ṫ {i : Size} : Set

-- terminal term
data t {i : Size} : Set

data Ṫ {i : Size} : Set

data T {i : Size} : Set

data q : Set where
  -- monotone (\u)
  ⇈ : q
  -- antitone (\d)
  ⇊ : q
  -- constant (~)
  ~ : q
  -- unknown (\??)
  ⁇ : q
  -- selector (\S)
  § : q

data c : Set where
  cInt  : ℤ → c
  cBool : Bool → c

-- qualifier map (\Xi)
Ξ : Set  
Ξ = List q 

data SfPrimitive : Set where
  SfPlus : SfPrimitive -- + on integers
  SfMinus : SfPrimitive -- - on integers
  SfLess : SfPrimitive -- < on integers
  SfLeq  : SfPrimitive -- ≤ on integers
  SfOr : SfPrimitive -- ∨ on booleans
  SfAnd : SfPrimitive -- ∧ on booleans

-- ****** For now we use only well-formed ast's, meaning that qualifier maps match their enclosing
--        ambient environments, as do the domains of ambient maps, and also that the bodies of embedded sfuns are 
--        wellformed. Well-formedness is weaker than
--        well-typedness; a programmer may write a program which is not well-formed, but it will 
--        be rejected by the type checker. Well-formedness is preserved by single-step reduction. We make 
--        no attempt to implement operational semantics (substitution and reduction) for non-well-formed syntax.
data T {i : Size} where
  -- τ{t}
  RefBase : {j : Size< i} → (τ : τ) → (tPred : t {j}) → T {i}
  -- (x : A, ...) ⇒ A[Ξ]{t}
  SFun : {j : Size< i} → (formals : List (τ × t {j})) → (τResult : τ) 
         → (Ξ : Ξ) → (tPred : t {j}) → T {i}
  -- (x : T) → T
  Fun : {j : Size< i} → (TFormal : T {i}) → (TResult : T {i}) → T {i}
  -- ⟨x < t⟩ T
  Fix  : {j : Size< i} → (tCurrMetric : t {j}) → (TBody : T {j}) → T {i}

data Ṫ {i : Size} where 
  -- τ{ṫ}
  RefBase     : {j : Size< i} → (τ : τ) → (ṫPred : ṫ {i}) → Ṫ {i}
  -- τ[Ξ]{ṫ}
  QualRefBase : {j : Size< i} → (τResult : τ) → (Ξ : Ξ) → (ṫPred : ṫ {i}) → Ṫ{i}
  -- (x : A, ...) ⇒ A[Ξ]{t}
  -- note that the third component of each formal is actually a terminal term 
  SFun : {j : Size< i} → (formals : List (τ × ṫ {j})) → (τResult : τ) → (Ξ : Ξ) → (ṫPred : ṫ {j}) → Ṫ{i}
  -- (x : Ṫ) → Ṫ
  Fun  : {j : Size< i} → (ṪFormal : Ṫ {i}) → (ṪResult : Ṫ {i}) → Ṫ {i}
  -- ⟨x < ṫ⟩ Ṫ
  Fix  : {j : Size< i} → (ṫCurrMetric : ṫ {i}) → (ṪBody : Ṫ {i}) → Ṫ {i}

data t {i : Size} where 
  Constant : (c₀ : c) → t {i}
  SfConstant : SfPrimitive → t {i}
  Var : (n : ℕ) → t {i}
  -- (λ (x : T) t)
  -- Terminal function with one argument named x of type T, with body t
  Fun : {j : Size< i} → (TFormal : T {j}) → (tBody : t {j}) → t {i}
  -- (fix t x S y s)
  -- A recursive term abstraction, where t is the termination metric, x is a variable referring to the "next" termination
  -- metric, S is the type of the body of the recursive term, y is a self-reference for the recursive term,
  -- and s is the recursive term itself
  Fix : {j : Size< i} → (tCurrMetric : t {j}) → (TBody : T {j}) → 
        (tBody : t {j}) → t {i}
  -- (λλ (x : B ...) ṫ)
  SFun : {j : Size< i} → (formals : List (τ × t {j})) → (ṫBody : ṫ {j}) → t {i}
  -- t s
  -- Standard function application
  App : {j : Size< i} → (tFun : t {j}) → (tArg : t {j}) → t {i} 
  -- t [ s_1 s_2 ... s_n ] ã
  -- SFun application
  SApp : {j : Size< i} → (tFun : t {j}) → (tArgs : List (t {j})) → t {i}
  -- t ⟨s⟩
  -- fixpoint application, where t is a fixpoint abstraction and s is its next termination metric
  FixApp : {j : Size< i} → (tFix : t {j}) → (tNextMetric : t {j}) → t {i}
  -- if s then t else u
  -- An if expression, s is the condition, t is the then clause, and u is the else clause
  IfThenElse : {j : Size< i} → (tCond : t {j}) → (tThen : t {j}) → (tElse : t {j}) → t {i} 
  -- let x = s in t
  Let : {j : Size< i} → (tBind : t {j}) → (tScope : t {j}) → t {i}

data ṫ {i : Size} where
  Constant : (c : c) → ṫ {i}
  SfConstant : SfPrimitive → ṫ {i}
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
  SFun : {j : Size< i} → (formals : List (τ × ṫ {j})) → (ṫBody : ṫ {j}) → ṫ {i}
  -- ṫ ṡ
  -- Standard function application
  App : {j : Size< i} → (ṫFun : ṫ {j}) → (ṫArg : ṫ {j}) → ṫ {i}
  -- ṫ [ ṡ_1 ṡ_2 ... ṡ_n ]
  -- SFun application
  SApp : {j : Size< i} → (ṫFun : ṫ {j}) → (ṫArgs : List (ṫ {j})) → ṫ {i}
  -- ṫ ⟨ṡ⟩
  -- fixpoint application, where ṫ is a fixpoint abstraction and ṡ is its next termination metric
  FixApp : {j : Size< i} → (ṫFix : ṫ {j}) → (ṫNextMetric : ṫ {j}) → ṫ {i}
  -- if ṫ₀ then ṫ₁ else ṫ₂
  -- An if expression, ṫ_0 is the condition, ṫ₁ is the then clause, and ṫ₂ is the else clause
  IfThenElse : {j : Size< i} → (ṫCond : ṫ {j}) → (ṫThen : ṫ {j}) → (ṫElse : ṫ {j}) → ṫ {i} 
  -- let x = ṡ in ṫ
  Let : {j : Size< i} → (ṫBind : ṫ {j}) → (ṫScope : ṫ {j}) → ṫ {i}

trueT : T
trueT = RefBase τBool (Constant (cBool true))

liftTy : T → Ṫ
liftTy aaa = RefBase τInt (Var 0)


⌈_⌉Ṫ : {i : Size} → T {i} → Ṫ {∞}

⌈_⌉ṫ : {j : Size} → t {j} → ṫ {∞}


⌈ Constant c ⌉ṫ = Constant c
⌈ SfConstant c ⌉ṫ = SfConstant c
⌈ Var n ⌉ṫ = Var n
⌈ Fun TFormal tBody ⌉ṫ =  Fun ⌈ TFormal ⌉Ṫ ⌈ tBody ⌉ṫ
⌈ Fix tCurrMetric TBody tBody ⌉ṫ =
  Fix ⌈ tCurrMetric ⌉ṫ ⌈ TBody ⌉Ṫ ⌈ tBody ⌉ṫ 
⌈ SFun formals ṫBody ⌉ṫ = SFun (L.map mapFormal formals) ṫBody
  where 
    mapFormal : τ × t → τ × ṫ
    mapFormal (τ , t) = (τ , ⌈ t ⌉ṫ) 
⌈ App tFun tArg ⌉ṫ = App ⌈ tFun ⌉ṫ ⌈ tArg ⌉ṫ
⌈ SApp tFun tArgs ⌉ṫ =  SApp ⌈ tFun ⌉ṫ (L.map ⌈_⌉ṫ tArgs)
⌈ FixApp tFix tNextMetric ⌉ṫ = FixApp ⌈ tFix ⌉ṫ ⌈ tNextMetric ⌉ṫ
⌈ IfThenElse tCond tThen tElse ⌉ṫ =  IfThenElse ⌈ tCond ⌉ṫ ⌈ tThen ⌉ṫ ⌈ tElse ⌉ṫ
⌈ Let tBind tScope ⌉ṫ = Let ⌈ tBind ⌉ṫ ⌈ tScope ⌉ṫ

⌈ RefBase τ t ⌉Ṫ = RefBase τ ⌈ t ⌉ṫ
⌈ SFun formals τBaseTy Ξ tPred ⌉Ṫ =  SFun (L.map mapFormal formals) τBaseTy Ξ ⌈ tPred ⌉ṫ
  where
    mapFormal : {i : Size} → τ × t {i} → τ × ṫ {∞}
    mapFormal (τ , t) = (τ , ⌈ t ⌉ṫ)
⌈ Fun TFormal TResult ⌉Ṫ = Fun ⌈ TFormal ⌉Ṫ ⌈ TResult ⌉Ṫ
⌈ Fix tCurrMetric TBody ⌉Ṫ = Fix ⌈ tCurrMetric ⌉ṫ ⌈ TBody ⌉Ṫ

-- the predicate variable is typed as \bigstar
-- predVar : var
-- predVar = "★" 

stub_ṫ : ṫ
stub_ṫ = (Constant (cBool true))

stub_t : t
stub_t = (Constant (cBool true))

testType1 : Ṫ
testType1 = SFun L.[ (τInt , (Constant (cInt -[1+ 10 ]))) ] τInt  L.[ ⇈ ] stub_ṫ

idt : Ṫ → Ṫ
idt x = x

testTerm1 : Ṫ
testTerm1 = idt (RefBase τInt stub_ṫ)


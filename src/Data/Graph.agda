module Data.Graph where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat
open import Data.Product
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail; init; last)
open import Data.Vec.Properties
import Level as ℓ
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open IsFinite

record FiniteGraph ℓᵥ ℓₑ : Set (ℓ.suc ℓᵥ ℓ.⊔ ℓ.suc ℓₑ) where
  constructor finiteGraph
  field
    {Vertex} : Set ℓᵥ
    {Edge} : Vertex → Vertex → Set ℓₑ
    vertexFinite : IsFinite Vertex
    decEqVertex : (a b : Vertex) → Dec (a ≡ b)
    edgeFinite : ∀ a → IsFinite (∃ (Edge a))

  infixr 5 _∷ʳ_
  data SizedPathʳ a : Vertex → ℕ → Set (ℓᵥ ℓ.⊔ ℓₑ) where
    [] : SizedPathʳ a a zero
    _∷_ : ∀ {b c n} → Edge b c → SizedPathʳ a b n → SizedPathʳ a c (suc n)

  data SizedPathˡ a : Vertex → ℕ → Set (ℓᵥ ℓ.⊔ ℓₑ) where
    [] : SizedPathˡ a a zero
    _∷_ : ∀ {b c n} → Edge a b → SizedPathˡ b c n → SizedPathˡ a c (suc n)

  Pathˡ≤ = λ a b n → ∃ λ m → m ≤ n × SizedPathˡ a b m
  Pathˡ< = λ a b n → ∃ λ m → m < n × SizedPathˡ a b m

  _∷ʳ_ : ∀ {a b c n} → SizedPathˡ a b n → Edge b c → SizedPathˡ a c (suc n)
  [] ∷ʳ e = e ∷ []
  (e ∷ p) ∷ʳ e′ = e ∷ p ∷ʳ e′

  infixr 5 _∷ˡ_
  _∷ˡ_ : ∀ {a b c n} → Edge a b → SizedPathʳ b c n → SizedPathʳ a c (suc n)
  e ∷ˡ [] = e ∷ []
  e ∷ˡ e′ ∷ p = e′ ∷ e ∷ˡ p

  infixl 5 _++ˡ_
  _++ˡ_ : ∀ {a b c m n} → SizedPathˡ a b m → SizedPathˡ b c n → SizedPathˡ a c (m + n)
  [] ++ˡ q = q
  (e ∷ p) ++ˡ q = e ∷ (p ++ˡ q)

  flipSizedPathˡ : ∀ {a b n} → SizedPathˡ a b n → SizedPathʳ a b n
  flipSizedPathˡ [] = []
  flipSizedPathˡ (e ∷ p) = e ∷ˡ flipSizedPathˡ p

  flipSizedPathʳ : ∀ {a b n} → SizedPathʳ a b n → SizedPathˡ a b n
  flipSizedPathʳ [] = []
  flipSizedPathʳ (e ∷ p) = flipSizedPathʳ p ∷ʳ e

  trailʳ : ∀ {a b n} → SizedPathʳ a b n → Vec Vertex (suc n)
  trailʳ {a} [] = Vec.[ a ]
  trailʳ {b = b} (e ∷ p) = b ∷ trailʳ p

  trailˡ : ∀ {a b n} → SizedPathˡ a b n → Vec Vertex n
  trailˡ [] = []
  trailˡ {a} (e ∷ p) = a ∷ trailˡ p

  data Pathʳ a : Vertex → Set (ℓᵥ ℓ.⊔ ℓₑ) where
    [] : Pathʳ a a
    _∷_ : ∀ {b c} → Edge b c → Pathʳ a b → Pathʳ a c

  data Pathˡ a : Vertex → Set (ℓᵥ ℓ.⊔ ℓₑ) where
    [] : Pathˡ a a
    _∷_ : ∀ {b c} → Edge a b → Pathˡ b c → Pathˡ a c

  fromSizedʳ : ∀ {a b n} → SizedPathʳ a b n → Pathʳ a b
  fromSizedʳ [] = []
  fromSizedʳ (e ∷ p) = e ∷ fromSizedʳ p

  fromSizedˡ : ∀ {a b n} → SizedPathˡ a b n → Pathˡ a b
  fromSizedˡ [] = []
  fromSizedˡ (e ∷ p) = e ∷ fromSizedˡ p

  sizeʳ : ∀ {a b} → Pathʳ a b → ℕ
  sizeʳ [] = zero
  sizeʳ (e ∷ p) = suc (sizeʳ p)

  sizeˡ : ∀ {a b} → Pathˡ a b → ℕ
  sizeˡ [] = zero
  sizeˡ (e ∷ p) = suc (sizeˡ p)

  toSizedʳ : ∀ {a b} (p : Pathʳ a b) → SizedPathʳ a b (sizeʳ p)
  toSizedʳ [] = []
  toSizedʳ (e ∷ p) = e ∷ toSizedʳ p

  toSizedˡ : ∀ {a b} (p : Pathˡ a b) → SizedPathˡ a b (sizeˡ p)
  toSizedˡ [] = []
  toSizedˡ (e ∷ p) = e ∷ toSizedˡ p

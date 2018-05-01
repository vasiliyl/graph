module Data.Graph where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail; init; last)
open import Data.Vec.Properties
open import Level as ℓ using (Level; _⊔_)
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open IsFinite

infix 3 _⊑[_]_
_⊑[_]_ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {A : Set ℓ₁} {B : Set ℓ₂} → (A → A → Set ℓ₃) → (A → B) → (B → B → Set ℓ₄) → Set _
_↦_ ⊑[ f ] _↦′_ = ∀ {i j} → i ↦ j → f i ↦′ f j

module Path {ℓᵥ ℓₑ} {V : Set ℓᵥ} (_↦_ : V → V → Set ℓₑ) where
  infixr 5 _∷ʳ_
  data SizedPathʳ a : V → ℕ → Set (ℓᵥ ⊔ ℓₑ) where
    [] : SizedPathʳ a a zero
    _∷_ : ∀ {b c n} → b ↦ c → SizedPathʳ a b n → SizedPathʳ a c (suc n)

  data SizedPathˡ a : V → ℕ → Set (ℓᵥ ⊔ ℓₑ) where
    [] : SizedPathˡ a a zero
    _∷_ : ∀ {b c n} → a ↦ b → SizedPathˡ b c n → SizedPathˡ a c (suc n)

  data Pathʳ a : V → Set (ℓᵥ ⊔ ℓₑ) where
    [] : Pathʳ a a
    _∷_ : ∀ {b c} → b ↦ c → Pathʳ a b → Pathʳ a c

  data Pathˡ a : V → Set (ℓᵥ ⊔ ℓₑ) where
    [] : Pathˡ a a
    _∷_ : ∀ {b c} → a ↦ b → Pathˡ b c → Pathˡ a c

  Pathˡ≤ = λ a b n → ∃ λ m → m ≤ n × SizedPathˡ a b m
  Pathˡ< = λ a b n → ∃ λ m → m < n × SizedPathˡ a b m

  _∷ʳ_ : ∀ {a b c n} → SizedPathˡ a b n → b ↦ c → SizedPathˡ a c (suc n)
  [] ∷ʳ e = e ∷ []
  (e ∷ p) ∷ʳ e′ = e ∷ p ∷ʳ e′

  infixr 5 _∷ˡ_
  _∷ˡ_ : ∀ {a b c n} → a ↦ b → SizedPathʳ b c n → SizedPathʳ a c (suc n)
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

  trailʳ : ∀ {a b n} → SizedPathʳ a b n → Vec V (suc n)
  trailʳ {a} [] = Vec.[ a ]
  trailʳ {b = b} (e ∷ p) = b ∷ trailʳ p

  trailˡ : ∀ {a b n} → SizedPathˡ a b n → Vec V n
  trailˡ [] = []
  trailˡ {a} (e ∷ p) = a ∷ trailˡ p

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

module Embed {ℓᵥ ℓᵥ′ ℓₑ ℓₑ′}
  {V : Set ℓᵥ} {V′ : Set ℓᵥ′} {_↦_ : V → V → Set ℓₑ} {_↦′_ : V′ → V′ → Set ℓₑ′} {f}
  (r : _↦_ ⊑[ f ] _↦′_) where

  open Path

  embedSizedPathʳ : ∀ {a b n} → SizedPathʳ _↦_ a b n → SizedPathʳ _↦′_ (f a) (f b) n
  embedSizedPathʳ [] = []
  embedSizedPathʳ (e ∷ es) = r e ∷ embedSizedPathʳ es

  embedSizedPathˡ : ∀ {a b n} → SizedPathˡ _↦_ a b n → SizedPathˡ _↦′_ (f a) (f b) n
  embedSizedPathˡ [] = []
  embedSizedPathˡ (e ∷ es) = r e ∷ embedSizedPathˡ es

  embedPathˡ : ∀ {a b} → Pathˡ _↦_ a b → Pathˡ _↦′_ (f a) (f b)
  embedPathˡ [] = []
  embedPathˡ (e ∷ es) = r e ∷ embedPathˡ es

  embedPathʳ : ∀ {a b} → Pathʳ _↦_ a b → Pathʳ _↦′_ (f a) (f b)
  embedPathʳ [] = []
  embedPathʳ (e ∷ es) = r e ∷ embedPathʳ es

record FiniteGraph ℓᵥ ℓₑ : Set (ℓ.suc ℓᵥ ⊔ ℓ.suc ℓₑ) where
  field
    {Vertex} : Set ℓᵥ
    {Edge} : Vertex → Vertex → Set ℓₑ
    {{vertexFinite}} : IsFinite Vertex
    {{edgeFinite}} : ∀ a → IsFinite (∃ (Edge a))
    decEqVertex : (a b : Vertex) → Dec (a ≡ b)

  open Path Edge public

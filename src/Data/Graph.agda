module Data.Graph where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat hiding (_⊔_)
open import Data.Product
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Properties
open import Level as ℓ using (Level; _⊔_)
open import Finite
open import Function
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open IsFinite

module Path {ℓᵥ ℓₑ} {V : Set ℓᵥ} (_↦_ : V → V → Set ℓₑ) where
  infixr 5 _∷ʳ_
  data Pathʳ a : V → ℕ → Set (ℓᵥ ⊔ ℓₑ) where
    [] : Pathʳ a a zero
    _∷_ : ∀ {b c n} → b ↦ c → Pathʳ a b n → Pathʳ a c (suc n)

  data Pathˡ a : V → ℕ → Set (ℓᵥ ⊔ ℓₑ) where
    [] : Pathˡ a a zero
    _∷_ : ∀ {b c n} → a ↦ b → Pathˡ b c n → Pathˡ a c (suc n)

  Pathˡ≤ = λ a b n → ∃ λ m → m ≤ n × Pathˡ a b m
  Pathˡ< = λ a b n → ∃ λ m → m < n × Pathˡ a b m

  _∷ʳ_ : ∀ {a b c n} → Pathˡ a b n → b ↦ c → Pathˡ a c (suc n)
  [] ∷ʳ e = e ∷ []
  (e ∷ p) ∷ʳ e′ = e ∷ p ∷ʳ e′

  infixr 5 _∷ˡ_
  _∷ˡ_ : ∀ {a b c n} → a ↦ b → Pathʳ b c n → Pathʳ a c (suc n)
  e ∷ˡ [] = e ∷ []
  e ∷ˡ e′ ∷ p = e′ ∷ e ∷ˡ p

  infixl 5 _++ˡ_
  _++ˡ_ : ∀ {a b c m n} → Pathˡ a b m → Pathˡ b c n → Pathˡ a c (m + n)
  [] ++ˡ q = q
  (e ∷ p) ++ˡ q = e ∷ (p ++ˡ q)

  flipPathˡ : ∀ {a b n} → Pathˡ a b n → Pathʳ a b n
  flipPathˡ [] = []
  flipPathˡ (e ∷ p) = e ∷ˡ flipPathˡ p

  flipPathʳ : ∀ {a b n} → Pathʳ a b n → Pathˡ a b n
  flipPathʳ [] = []
  flipPathʳ (e ∷ p) = flipPathʳ p ∷ʳ e

  id≗flipPathʳ∘flipPathˡ : ∀ {a b n} → id ≗ flipPathʳ {a} {b} {n} ∘ flipPathˡ
  id≗flipPathʳ∘flipPathˡ [] = refl
  id≗flipPathʳ∘flipPathˡ (e ∷ p) =
    trans
      (cong (e ∷_) (id≗flipPathʳ∘flipPathˡ p))
      (step e (flipPathˡ p))
    where
      step : ∀ {a b c n} (e : a ↦ b) (p : Pathʳ b c n) → e ∷ flipPathʳ p ≡ flipPathʳ (e ∷ˡ p)
      step e [] = refl
      step e (e′ ∷ p) = cong (_∷ʳ e′) (step e p)

  trailʳ : ∀ {a b n} → Pathʳ a b n → Vec V (suc n)
  trailʳ {a} [] = Vec.[ a ]
  trailʳ {b = b} (e ∷ p) = b ∷ trailʳ p

  trailˡ : ∀ {a b n} → Pathˡ a b n → Vec V n
  trailˡ [] = []
  trailˡ {a} (e ∷ p) = a ∷ trailˡ p

  toStarʳ : ∀ {a b n} → Pathʳ a b n → Star _↦_ a b
  toStarʳ [] = ε
  toStarʳ (e ∷ p) = toStarʳ p ◅◅ e ◅ ε

  toStarˡ : ∀ {a b n} → Pathˡ a b n → Star _↦_ a b
  toStarˡ [] = ε
  toStarˡ (e ∷ p) = e ◅ toStarˡ p

  starLength : ∀ {a b} → Star _↦_ a b → ℕ
  starLength = fold _ (const suc) zero

  fromStarˡ : ∀ {a b} (p : Star _↦_ a b) → Pathˡ a b (starLength p)
  fromStarˡ ε = []
  fromStarˡ (e ◅ p) = e ∷ fromStarˡ p

  fromStarʳ : ∀ {a b} (p : Star _↦_ a b) → Pathʳ a b (starLength p)
  fromStarʳ = flipPathˡ ∘ fromStarˡ

module Embed {ℓᵥ ℓᵥ′ ℓₑ ℓₑ′}
  {V : Set ℓᵥ} {V′ : Set ℓᵥ′} {_↦_ : V → V → Set ℓₑ} {_↦′_ : V′ → V′ → Set ℓₑ′} {f}
  (r : _↦_ =[ f ]⇒ _↦′_) where

  open Path

  embedPathʳ : ∀ {a b n} → Pathʳ _↦_ a b n → Pathʳ _↦′_ (f a) (f b) n
  embedPathʳ [] = []
  embedPathʳ (e ∷ es) = r e ∷ embedPathʳ es

  embedPathˡ : ∀ {a b n} → Pathˡ _↦_ a b n → Pathˡ _↦′_ (f a) (f b) n
  embedPathˡ [] = []
  embedPathˡ (e ∷ es) = r e ∷ embedPathˡ es

record FiniteGraph ℓᵥ ℓₑ : Set (ℓ.suc ℓᵥ ⊔ ℓ.suc ℓₑ) where
  field
    {Vertex} : Set ℓᵥ
    {Edge} : Vertex → Vertex → Set ℓₑ
    {{vertexFinite}} : IsFinite Vertex
    {{edgeFinite}} : ∀ a → IsFinite (∃ (Edge a))
    decEqVertex : (a b : Vertex) → Dec (a ≡ b)

  open Path Edge public

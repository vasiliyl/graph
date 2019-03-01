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
  data Path a : V → ℕ → Set (ℓᵥ ⊔ ℓₑ) where
    [] : Path a a zero
    _∷_ : ∀ {b c n} → a ↦ b → Path b c n → Path a c (suc n)

  Path≤ = λ a b n → ∃ λ m → m ≤ n × Path a b m
  Path< = λ a b n → ∃ λ m → m < n × Path a b m

  infixr 5 _∷ʳ_
  _∷ʳ_ : ∀ {a b c n} → Path a b n → b ↦ c → Path a c (suc n)
  [] ∷ʳ e = e ∷ []
  (e ∷ p) ∷ʳ e′ = e ∷ p ∷ʳ e′

  unsnoc : ∀ {n a c}
    (p : Path a c (suc n)) →
    ∃ λ b →
      ∃₂ λ (p′ : Path a b n) (e : b ↦ c) →
        p ≡ p′ ∷ʳ e
  unsnoc (e ∷ []) = -, [] , e , refl
  unsnoc (e ∷ d ∷ p) with unsnoc (d ∷ p)
  … | b , p′ , e′ , eq rewrite eq = b , e ∷ p′ , e′ , refl

  infixl 5 _++_
  _++_ : ∀ {a b c m n} → Path a b m → Path b c n → Path a c (m + n)
  [] ++ q = q
  (e ∷ p) ++ q = e ∷ (p ++ q)

  trail : ∀ {a b n} → Path a b n → Vec V n
  trail [] = []
  trail {a} (e ∷ p) = a ∷ trail p

  toStar : ∀ {a b n} → Path a b n → Star _↦_ a b
  toStar [] = ε
  toStar (e ∷ p) = e ◅ toStar p

  starLength : ∀ {a b} → Star _↦_ a b → ℕ
  starLength = fold _ (const suc) zero

  fromStar : ∀ {a b} (p : Star _↦_ a b) → Path a b (starLength p)
  fromStar ε = []
  fromStar (e ◅ p) = e ∷ fromStar p

module Embed {ℓᵥ ℓᵥ′ ℓₑ ℓₑ′}
  {V : Set ℓᵥ} {V′ : Set ℓᵥ′} {_↦_ : V → V → Set ℓₑ} {_↦′_ : V′ → V′ → Set ℓₑ′} {f}
  (r : _↦_ =[ f ]⇒ _↦′_) where

  open Path

  embedPath : ∀ {a b n} → Path _↦_ a b n → Path _↦′_ (f a) (f b) n
  embedPath [] = []
  embedPath (e ∷ es) = r e ∷ embedPath es

record FiniteGraph ℓᵥ ℓₑ : Set (ℓ.suc ℓᵥ ⊔ ℓ.suc ℓₑ) where
  field
    {Vertex} : Set ℓᵥ
    {Edge} : Vertex → Vertex → Set ℓₑ
    {{vertexFinite}} : IsFinite Vertex
    {{edgeFinite}} : ∀ a → IsFinite (∃ (Edge a))
    decEqVertex : (a b : Vertex) → Dec (a ≡ b)

  open Path Edge public

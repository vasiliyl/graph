{-# OPTIONS --type-in-type #-}

module Graph where

open import Data.List using (List; []; _∷_)
open import Data.Nat
open import Data.Product
open import Data.Vec using (Vec; []; _∷_)
open import Finite
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open IsFinite

record IsFiniteGraph {V} (E : V → V → Set) : Set where
  field
    vertexFinite : IsFinite V
    decEqVertex : (a b : V) → Dec (a ≡ b)
    edgeFinite : ∀ a → IsFinite (∃ (E a))

record FiniteGraph : Set  where
  field
    {Vertex} : Set
    {Edge} : Vertex → Vertex → Set
    isFiniteGraph : IsFiniteGraph Edge

  open IsFiniteGraph isFiniteGraph public

  infix 2 _⇒_
  _⇒_ = Edge

  infixr 5 _∷ʳ_
  data Pathʳ a : Vertex → ℕ → Set where
    [] : Pathʳ a a zero
    _∷_ : ∀ {b c n} → Pathʳ a b n → b ⇒ c → Pathʳ a c (suc n)

  data Pathˡ a : Vertex → ℕ → Set where
    [] : Pathˡ a a zero
    _∷_ : ∀ {b c n} → a ⇒ b → Pathˡ b c n → Pathˡ a c (suc n)

  Pathˡ≤ = λ a b n → ∃ λ m → m ≤ n × Pathˡ a b m
  Pathˡ< = λ a b n → ∃ λ m → m < n × Pathˡ a b m

  _∷ʳ_ : ∀ {a b c n} → Pathˡ a b n → b ⇒ c → Pathˡ a c (suc n)
  [] ∷ʳ e = e ∷ []
  (e ∷ p) ∷ʳ e′ = e ∷ (p ∷ʳ e′)

  infixr 5 _∷ˡ_
  _∷ˡ_ : ∀ {a b c n} → a ⇒ b → Pathʳ b c n → Pathʳ a c (suc n)
  e ∷ˡ [] = [] ∷ e
  e ∷ˡ p ∷ e′ = (e ∷ˡ p) ∷ e′

  infixl 5 _++ˡ_
  _++ˡ_ : ∀ {a b c m n} → Pathˡ a b m → Pathˡ b c n → Pathˡ a c (m + n)
  [] ++ˡ q = q
  (e ∷ p) ++ˡ q = e ∷ (p ++ˡ q)

  reversePathˡ : ∀ {a b n} → Pathˡ a b n → Pathʳ a b n
  reversePathˡ [] = []
  reversePathˡ (e ∷ p) = e ∷ˡ reversePathˡ p

  reversePathʳ : ∀ {a b n} → Pathʳ a b n → Pathˡ a b n
  reversePathʳ [] = []
  reversePathʳ (p ∷ e) = reversePathʳ p ∷ʳ e

  trailʳ : ∀ {a b n} → Pathʳ a b n → Vec Vertex n
  trailʳ [] = []
  trailʳ {b = c} (p ∷ e) = c ∷ trailʳ p

  trailˡ : ∀ {a b n} → Pathˡ a b n → Vec Vertex n
  trailˡ [] = []
  trailˡ {a} (e ∷ p) = a ∷ trailˡ p

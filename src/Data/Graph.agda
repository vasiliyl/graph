{-# OPTIONS --type-in-type #-}

module Data.Graph where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat
open import Data.Product
open import Data.Vec as Vec using (Vec; []; _∷_; head; tail; init; last)
open import Data.Vec.Properties
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open IsFinite

record FiniteGraph : Set  where
  constructor finiteGraph
  field
    {Vertex} : Set
    {Edge} : Vertex → Vertex → Set
    vertexFinite : IsFinite Vertex
    decEqVertex : (a b : Vertex) → Dec (a ≡ b)
    edgeFinite : ∀ a → IsFinite (∃ (Edge a))

  infix 2 _⇒_
  _⇒_ = Edge

  infixr 5 _∷ʳ_
  data Pathʳ a : Vertex → ℕ → Set where
    [] : Pathʳ a a zero
    _∷_ : ∀ {b c n} → Pathʳ a b n → b ⇒ c → Pathʳ a c (suc n)

  data Trailʳ : ∀ {n} → Vec Vertex n → Set where
    [] : ∀ {a} → Trailʳ Vec.[ a ]
    _∷_ : ∀ {a b n} {as : Vec _ n} → Trailʳ (a ∷ as) → a ⇒ b → Trailʳ (b ∷ a ∷ as)

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

  trailʳ : ∀ {a b n} → Pathʳ a b n → Vec Vertex (suc n)
  trailʳ {a} [] = Vec.[ a ]
  trailʳ {b = b} (p ∷ e) = b ∷ trailʳ p

  trailˡ : ∀ {a b n} → Pathˡ a b n → Vec Vertex n
  trailˡ [] = []
  trailˡ {a} (e ∷ p) = a ∷ trailˡ p

  trailHeadʳ : ∀ {a b n} (p : Pathʳ a b n) → head (trailʳ p) ≡ b
  trailHeadʳ [] = refl
  trailHeadʳ (p ∷ e) = refl

  pathToTrailʳ : ∀ {a b n} (p : Pathʳ a b n) → Trailʳ (trailʳ p)
  pathToTrailʳ [] = []
  pathToTrailʳ (p ∷ e) with trailʳ p | inspect trailʳ p
  … | d ∷ as | [ eq ] =
    subst Trailʳ eq (pathToTrailʳ p) ∷
      subst (_⟨ Edge ⟩ _) (sym (trans (cong head (sym eq)) (trailHeadʳ p))) e

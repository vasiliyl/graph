{-# OPTIONS --type-in-type #-}

open import Graph

module Graph.Path.Search (g : FiniteGraph) where

open import Data.Product
open import Finite
open import Function
open import Graph.Cut.Path g
open import Graph.Path.Finite g
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open FiniteGraph g
open IsFinite

∃Pathˡ? : ∀ {P : Vertex → Set}
  a → (∀ x → Dec (P x)) → Dec (∃ λ b → ∃ (Pathˡ a b) × P b)
∃Pathˡ? a P? =
  case ∃? (Pathˡ≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , (_ , _ , p)) , pb)) → yes (, (, p) , pb)
    (no ¬p) → no λ where (_ , (_ , p) , pb) → ¬p ((, shortEnoughPath p) , pb)

Pathˡ? : ∀ a b → Dec (∃ (Pathˡ a b))
Pathˡ? a b =
  case ∃Pathˡ? a (decEqVertex b) of λ where
    (yes (_ , p , refl)) → yes (, proj₂ p)
    (no ¬p) → no λ p → ¬p (, p , refl)

∃Pathʳ? : ∀ {P : Vertex → Set}
  a → (∀ x → Dec (P x)) → Dec (∃ λ b → ∃ (Pathʳ a b) × P b)
∃Pathʳ? a P? =
  case ∃Pathˡ? a P? of λ where
    (yes (_ , (_ , p) , pb)) → yes (, (, reversePathˡ p) , pb)
    (no ¬p) → no λ where (b , (_ , p) , pb) → ¬p (, (, reversePathʳ p) , pb)

Pathʳ? : ∀ a b → Dec (∃ (Pathʳ a b))
Pathʳ? a b =
  case Pathˡ? a b of λ where
    (yes (n , p)) → yes (n , reversePathˡ p)
    (no ¬p) → no λ where (n , p) → ¬p (n , reversePathʳ p)

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

Pathˡ? : ∀ a b → Dec (∃ (Pathˡ a b))
Pathˡ? a b =
  case ∃? (Pathˡ≤-finite (size vertexFinite) a) (decEqVertex b ∘ proj₁) of λ where
    (yes ((_ , m , le , p) , refl)) → yes (, p)
    (no ¬p) → no λ where (n , p) → ¬p ((, shortEnoughPath p) , refl)

Pathʳ? : ∀ a b → Dec (∃ (Pathʳ a b))
Pathʳ? a b =
  case Pathˡ? a b of λ where
    (yes (n , p)) → yes (n , reversePathˡ p)
    (no ¬p) → no λ where (n , p) → ¬p (n , reversePathʳ p)

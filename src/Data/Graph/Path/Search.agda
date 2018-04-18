open import Data.Graph

module Data.Graph.Path.Search {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Graph.Cut.Path g
open import Data.Graph.Path.Finite g
open import Data.Product
open import Finite
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open FiniteGraph g
open IsFinite

sizedSearchFromˡ : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × ∃ (SizedPathˡ a b))
sizedSearchFromˡ P? a =
  case ∃? (SizedPathˡ≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) → yes (, pb , (, p))
    (no ¬p) → no λ where (_ , pb , _ , p) → ¬p ((, shortEnoughPath p) , pb)

sizedSearchFromʳ : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × ∃ (SizedPathʳ a b))
sizedSearchFromʳ P? a =
  case sizedSearchFromˡ P? a of λ where
    (yes (_ , pb , _ , p)) → yes (, pb , , flipSizedPathˡ p)
    (no ¬p) → no λ where (_ , pb , _ , p) → ¬p (, pb , , flipSizedPathʳ p)

sizedSearchBetweenˡ : ∀ a b → Dec (∃ (SizedPathˡ a b))
sizedSearchBetweenˡ a b =
  case sizedSearchFromˡ (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where (n , p) → ¬p (, refl , , p)

sizedSearchBetweenʳ : ∀ a b → Dec (∃ (SizedPathʳ a b))
sizedSearchBetweenʳ a b =
  case sizedSearchFromʳ (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where (n , p) → ¬p (, refl , , p)

searchFromˡ : ∀ {ℓ} {P : Vertex → Set ℓ} → (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × Pathˡ a b)
searchFromˡ P? a =
  case sizedSearchFromˡ P? a of λ where
    (yes (_ , pb , _ , p)) → yes (, pb , fromSizedˡ p)
    (no ¬p) → no λ where (_ , pb , p) → ¬p (, pb , , toSizedˡ p)

searchBetweenˡ : ∀ a b → Dec (Pathˡ a b)
searchBetweenˡ a b =
  case searchFromˡ (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where p → ¬p (, refl , p)

searchFromʳ : ∀ {ℓ} {P : Vertex → Set ℓ} → (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × Pathʳ a b)
searchFromʳ P? a =
  case sizedSearchFromʳ P? a of λ where
    (yes (_ , pb , _ , p)) → yes (, pb , fromSizedʳ p)
    (no ¬p) → no λ where (_ , pb , p) → ¬p (, pb , , toSizedʳ p)

searchBetweenʳ : ∀ a b → Dec (Pathʳ a b)
searchBetweenʳ a b =
  case searchFromʳ (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where p → ¬p (, refl , p)

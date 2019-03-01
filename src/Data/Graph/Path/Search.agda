open import Data.Graph

module Data.Graph.Path.Search {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Graph.Cut.Path g
open import Data.Graph.Path.Finite g
open import Data.Product
open import Finite
open import Finite.Pigeonhole
open import Function
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open FiniteGraph g
open IsFinite

¬-dec : ∀ {ℓ} {A : Set ℓ} → Dec A → Dec (¬ A)
¬-dec (yes p) = no λ ¬p → ¬p p
¬-dec (no ¬p) = yes ¬p

sizedSearchFromˡ : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × ∃ (Pathˡ a b))
sizedSearchFromˡ P? a =
  case ∃? (Pathˡ≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) → yes (-, pb , (-, p))
    (no ¬p) → no λ where (_ , pb , _ , p) → ¬p ((-, shortEnoughPath p) , pb)

sizedSearchAcyclicFromˡ : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a →
  Dec (∃ λ b →
    P b ×
      ∃₂ λ n (p : Pathˡ a b n) →
        ¬ Repeats (trailˡ p))
sizedSearchAcyclicFromˡ P? a =
  case ∃? (Pathˡ≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) →
      let (x , x≤n , p′) , ¬r′ = acyclicPath p in
        yes (-, pb , (-, (p′ , ¬r′)))
    (no ¬p) → no λ where (_ , pb , _ , p , r) → ¬p ((-, shortEnoughPath p) , pb)

sizedSearchFromʳ : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × ∃ (Pathʳ a b))
sizedSearchFromʳ P? a =
  case sizedSearchFromˡ P? a of λ where
    (yes (_ , pb , _ , p)) → yes (-, pb , -, flipPathˡ p)
    (no ¬p) → no λ where (_ , pb , _ , p) → ¬p (-, pb , -, flipPathʳ p)

sizedSearchBetweenˡ : ∀ a b → Dec (∃ (Pathˡ a b))
sizedSearchBetweenˡ a b =
  case sizedSearchFromˡ (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where (n , p) → ¬p (-, refl , -, p)

sizedSearchBetweenʳ : ∀ a b → Dec (∃ (Pathʳ a b))
sizedSearchBetweenʳ a b =
  case sizedSearchFromʳ (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where (n , p) → ¬p (-, refl , -, p)

searchFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) →
  ∀ a → Dec (∃ λ b → P b × Star Edge a b)
searchFrom P? a =
  case sizedSearchFromˡ P? a of λ where
    (yes (_ , pb , _ , p)) → yes (-, pb , toStarˡ p)
    (no ¬p) → no λ where (_ , pb , p) → ¬p (-, pb , -, fromStarˡ p)

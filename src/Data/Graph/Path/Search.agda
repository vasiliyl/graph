open import Data.Graph

module Data.Graph.Path.Search {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Graph.Cut.Path g
open import Data.Graph.Path.Finite g
open import Data.Product as Σ
open import Finite
open import Finite.Pigeonhole
open import Function
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation as ¬

open FiniteGraph g
open IsFinite

pathSearchFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × ∃ (Path a b))
pathSearchFrom P? a =
  case ∃? (Path≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) → yes (-, pb , (-, p))
    (no ¬p) → no λ where (_ , pb , _ , p) → ¬p ((-, shortEnoughPath p) , pb)

pathSearchAcyclicFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a →
  Dec (∃ λ b →
    P b ×
      ∃₂ λ n (p : Path a b n) →
        ¬ Repeats (trail p))
pathSearchAcyclicFrom P? a =
  case ∃? (Path≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) →
      let (x , x≤n , p′) , ¬r′ = acyclicPath p in
        yes (-, pb , (-, (p′ , ¬r′)))
    (no ¬p) → no λ where (_ , pb , _ , p , r) → ¬p ((-, shortEnoughPath p) , pb)

pathSearchBetween : ∀ a b → Dec (∃ (Path a b))
pathSearchBetween a b =
  case pathSearchFrom (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where (n , p) → ¬p (-, refl , -, p)

searchFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) →
  ∀ a → Dec (∃ λ b → P b × Star Edge a b)
searchFrom P? a =
  Dec.map′
    (map₂ (map₂ (toStar ∘ proj₂)))
    (map₂ (map₂ (-,_ ∘ fromStar)))
    (pathSearchFrom P? a)

searchBetween : ∀ a b → Dec (Star Edge a b)
searchBetween a b = Dec.map′ (toStar ∘ proj₂) (-,_ ∘ fromStar) (pathSearchBetween a b)

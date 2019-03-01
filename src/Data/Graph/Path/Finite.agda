open import Data.Graph

module Data.Graph.Path.Finite {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Category.Monad
open import Data.Graph.Cut.Path g
open import Data.List as List hiding (_∷ʳ_)
open import Data.List.Any as Any
open import Data.List.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.List.Categorical as ListCat
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as ×
open import Data.Sum as ⊎
import Level as ℓ
open import Finite
open import Function
open import Function.Equality using (Π)
open import Function.Equivalence using (Equivalence)
open import Function.Inverse using (Inverse)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open Π using (_⟨$⟩_)
open Equivalence using (to; from)
open FiniteGraph g
open Inverse using (to; from)
open IsFinite
open RawMonad {ℓᵥ ℓ.⊔ ℓₑ} ListCat.monad

nexts : ∀ {a b n} → Pathʳ a b n → List (∃ λ b → Pathʳ a b (suc n))
nexts {a} {b} p = List.map (λ where (_ , e) → -, e ∷ p) (elements (edgeFinite b))

∈-nexts : ∀ {a c n} →
  (pf : IsFinite (∃ λ b → Pathʳ a b n)) →
  (p : Pathʳ a c (suc n)) →
  (c , p) ∈ (elements pf >>= (nexts ∘ proj₂))
∈-nexts pf (e ∷ p) =
  to {ℓᵥ ℓ.⊔ ℓₑ} >>=-∈↔ ⟨$⟩
    (-, membership pf (-, p) , to map-∈↔ ⟨$⟩ (-, membership (edgeFinite _) (-, e) , refl))

Pathʳ-finite : ∀ n a → IsFinite (∃ λ b → Pathʳ a b n)
Pathʳ-finite zero a = finite List.[ -, [] ] λ where (_ , []) → here refl
Pathʳ-finite (suc n) a =
  let pf = Pathʳ-finite n a in
    finite (elements pf >>= (nexts ∘ proj₂)) (∈-nexts pf ∘ proj₂)

Pathˡ-finite : ∀ n a → IsFinite (∃ λ b → Pathˡ a b n)
elements (Pathˡ-finite n a) = List.map (×.map id flipPathʳ) (elements (Pathʳ-finite n a))
membership (Pathˡ-finite n a) (b , p) =
  to map-∈↔ ⟨$⟩
    ((b , flipPathˡ p) ,
    membership (Pathʳ-finite n a) _ ,
    cong (b ,_) (id≗flipPathʳ∘flipPathˡ p))

≤-top? : ∀ {x y} → x ≤ suc y → x ≤ y ⊎ x ≡ suc y
≤-top? z≤n = inj₁ z≤n
≤-top? {y = zero} (s≤s z≤n) = inj₂ refl
≤-top? {y = suc y} (s≤s p) =
  case ≤-top? p of λ where
    (inj₁ le) → inj₁ (s≤s le)
    (inj₂ refl) → inj₂ refl

Pathˡ≤-finite : ∀ n a → IsFinite (∃ λ b → Pathˡ≤ a b n)
Pathˡ≤-finite zero a = finite List.[ -, -, z≤n , [] ] λ where (_ , _ , z≤n , []) → here refl
Pathˡ≤-finite (suc n) a =
  let
    finite xs elem = Pathˡ≤-finite n a
    finite xs′ elem′ = Pathˡ-finite (suc n) a
  in
    finite
      (List.map (×.map _ (×.map _ (×.map ≤-step id))) xs ++
        List.map (×.map id (_,_ (suc n) ∘ _,_ ≤-refl)) xs′)
      λ where
        (b , m , le , p) → case ≤-top? le of λ where
          (inj₁ le′) →
            to ++↔ ⟨$⟩
              inj₁
                (to map-∈↔ ⟨$⟩
                  (-, (elem (b , m , le′ , p)) ,
                    cong (λ q → b , m , q , p) (≤-irrelevance le (≤-step le′))))
          (inj₂ refl) →
            to (++↔ {xs = List.map _ xs}) ⟨$⟩
              inj₂
                (to map-∈↔ ⟨$⟩
                  (-, elem′ (-, p) ,
                    cong (λ q → b , m , q , p) (≤-irrelevance le (s≤s ≤-refl))))

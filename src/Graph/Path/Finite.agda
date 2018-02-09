{-# OPTIONS --type-in-type #-}

open import Graph

module Graph.Path.Finite (g : FiniteGraph) where

open import Category.Monad
open import Data.List as List hiding (_∷ʳ_)
open import Data.List.Any as Any
open import Data.List.Any.Membership.Propositional
open import Data.List.Any.Membership.Propositional.Properties hiding (finite)
open import Data.List.Any.Properties
open import Data.List.Categorical as ListCat
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as ×
open import Data.Sum as ⊎
open import Finite
open import Function
open import Function.Equality using (Π)
open import Function.Equivalence using (Equivalence)
open import Function.Inverse using (Inverse)
open import Graph.Cut.Path g
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open Π using (_⟨$⟩_)
open Equivalence using (to; from)
open FiniteGraph g
open Inverse using (to; from)
open IsFinite
open RawMonad ListCat.monad

nexts : ∀ {a b n} → Pathʳ a b n → List (∃ λ b → Pathʳ a b (suc n))
nexts {a} {b} p = List.map (λ where (_ , e) → , p ∷ e) (elements (edgeFinite b))

∈-nexts : ∀ {a c n} →
  (pf : IsFinite (∃ λ b → Pathʳ a b n)) →
  (p : Pathʳ a c (suc n)) →
  (c , p) ∈ (elements pf >>= (nexts ∘ proj₂))
∈-nexts pf (p ∷ e) =
  to >>=-∈↔ ⟨$⟩ (, membership pf (, p) , to map-∈↔ ⟨$⟩ (, membership (edgeFinite _) (, e) , refl))

Pathʳ-finite : ∀ n a → IsFinite (∃ λ b → Pathʳ a b n)
Pathʳ-finite zero a = finite List.[ , [] ] λ where (_ , []) → here refl
Pathʳ-finite (suc n) a =
  let pf = Pathʳ-finite n a in
    finite (elements pf >>= (nexts ∘ proj₂)) (∈-nexts pf ∘ proj₂)


id≗reversePathʳ∘reversePathˡ : ∀ {a b n} → id ≗ reversePathʳ {a} {b} {n} ∘ reversePathˡ
id≗reversePathʳ∘reversePathˡ [] = refl
id≗reversePathʳ∘reversePathˡ (e ∷ p) =
  trans
    (cong (e ∷_) (id≗reversePathʳ∘reversePathˡ p))
    (step e (reversePathˡ p))
  where
    step : ∀ {a b c n} (e : a ⇒ b) (p : Pathʳ b c n) → e ∷ reversePathʳ p ≡ reversePathʳ (e ∷ˡ p)
    step e [] = refl
    step e (p ∷ e′) = cong (_∷ʳ e′) (step e p)

Pathˡ-finite : ∀ n a → IsFinite (∃ λ b → Pathˡ a b n)
elements (Pathˡ-finite n a) = List.map (×.map id reversePathʳ) (elements (Pathʳ-finite n a))
membership (Pathˡ-finite n a) (b , p) =
  to map-∈↔ ⟨$⟩
    ((b , reversePathˡ p) ,
    membership (Pathʳ-finite n a) _ ,
    cong (_,_ b) (id≗reversePathʳ∘reversePathˡ p))

≤-top? : ∀ {x y} → x ≤ suc y → x ≤ y ⊎ x ≡ suc y
≤-top? z≤n = inj₁ z≤n
≤-top? {y = zero} (s≤s z≤n) = inj₂ refl
≤-top? {y = suc y} (s≤s p) =
  case ≤-top? p of λ where
    (inj₁ le) → inj₁ (s≤s le)
    (inj₂ refl) → inj₂ refl

Pathˡ≤-finite : ∀ n a → IsFinite (∃ λ b → Pathˡ≤ a b n)
Pathˡ≤-finite zero a = finite List.[ , , z≤n , [] ] λ where (_ , _ , z≤n , []) → here refl
Pathˡ≤-finite (suc n) a =
  let
    finite xs elem = Pathˡ≤-finite n a
    finite xs′ elem′ = Pathˡ-finite (suc n) a
  in
    finite
      (List.map (×.map _ (×.map _ (×.map ≤-step id))) xs List.++
        List.map (×.map id (_,_ (suc n) ∘ _,_ ≤-refl)) xs′)
      λ where
        (b , m , le , p) → case ≤-top? le of λ where
          (inj₁ le′) →
            to ++↔ ⟨$⟩
              inj₁
                (to map-∈↔ ⟨$⟩
                  (, (elem (b , m , le′ , p)) ,
                    cong (λ q → b , m , q , p) (≤-irrelevance le (≤-step le′))))
          (inj₂ refl) →
            to (++↔ {xs = List.map _ xs}) ⟨$⟩
              inj₂
                (to map-∈↔ ⟨$⟩
                  (, elem′ (, p) ,
                    cong (λ q → b , m , q , p) (≤-irrelevance le (s≤s ≤-refl))))

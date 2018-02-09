{-# OPTIONS --type-in-type #-}

open import Graph

module Graph.Cut.Path (g : FiniteGraph) where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Vec hiding (_∷ʳ_)
open import Finite
open import Function
open import Induction.Nat
open import Graph.Cut.Vec
open import Pigeonhole
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open FiniteGraph g
open IsFinite
open ≡-Reasoning

breakPath : ∀ {a b x l}
  (p : Pathˡ a b l)
  (e : x ∈ trailˡ p) →
  Pathˡ a x (prefixLength e) × Pathˡ x b (suc (suffixLength e))
breakPath [] ()
breakPath (e ∷ p) here = [] , e ∷ p
breakPath (e ∷ p) (there d) =
  let q , r = breakPath p d in
    e ∷ q , r

prefixPath : ∀ {a b x l}
  (p : Pathˡ a b l)
  (e : x ∈ trailˡ p) →
  Pathˡ a x _
prefixPath p = proj₁ ∘ breakPath p

suffixPath : ∀ {a b x l}
  (p : Pathˡ a b l)
  (e : x ∈ trailˡ p) →
  Pathˡ x b _
suffixPath p = proj₂ ∘ breakPath p

suffixLength≡suffixLength-tail : ∀ {a b x n}
  (p : Pathˡ a b n)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  suffixLength e′ ≡ suffixLength {xs = suffix e} (tail-⊆ e′)
suffixLength≡suffixLength-tail [] () e′
suffixLength≡suffixLength-tail (e ∷ p) here e′ = refl
suffixLength≡suffixLength-tail (e ∷ p) (there i) e′ = suffixLength≡suffixLength-tail p i e′

suffix≡suffixPath : ∀ {a b x l}
  (p : Pathˡ a b l)
  (e : x ∈ trailˡ p) →
  suffix e ≡ trailˡ (suffixPath p e)
suffix≡suffixPath [] ()
suffix≡suffixPath (e ∷ p) here = refl
suffix≡suffixPath (e ∷ p) (there i) = suffix≡suffixPath p i

segmentPath : ∀ {a b x l}
  (p : Pathˡ a b l)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  Pathˡ a x (prefixLength e) × Pathˡ x x (suc (prefixLength e′)) × Pathˡ x b (suc (suffixLength e′))
segmentPath p e e′ =
  let
    u , v = breakPath p e
    u′ , v′ = breakPath v (subst (_ ∈_) (suffix≡suffixPath p e) (tail-⊆ e′))
  in
    u ,
    subst (Pathˡ _ _) (prefixLengthLem p _ _) u′ ,
    subst (Pathˡ _ _) (cong suc (suffixLengthLem p _ _)) v′
  where
    prefixLengthLem : ∀ {a b x l}
      (p : Pathˡ a b l)
      (e : x ∈ trailˡ p)
      (e′ : x ∈ tail (suffix e)) →
      prefixLength (subst (_ ∈_) (suffix≡suffixPath p e) (tail-⊆ e′)) ≡ suc (prefixLength e′)
    prefixLengthLem [] () e′
    prefixLengthLem (e ∷ p) here e′ = refl
    prefixLengthLem (e ∷ p) (there i) e′ = prefixLengthLem p i e′

    suffixLengthLem : ∀ {a b x l}
      (p : Pathˡ a b l)
      (e : x ∈ trailˡ p)
      (e′ : x ∈ tail (suffix e)) →
      suffixLength (subst (_ ∈_) (suffix≡suffixPath p e) (tail-⊆ e′)) ≡ suffixLength e′
    suffixLengthLem [] () e′
    suffixLengthLem (e ∷ p) here e′ = refl
    suffixLengthLem (e ∷ p) (there i) e′′ = suffixLengthLem p i e′′

cutPathLoop : ∀ {a b x n}
  (p : Pathˡ a b n)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  Pathˡ< a b n
cutPathLoop {n = n} p e e′ = let u , v , w = segmentPath p e e′ in , lt , u ++ˡ w
  where
    lt : suc (prefixLength e) + suc (suffixLength e′) ≤ n
    lt = subst₂ _≤_
      (cong suc (begin
        (prefixLength e + suffixLength e′) + 1
      ≡⟨ +-assoc (prefixLength e) _ _ ⟩
        prefixLength e + (suffixLength e′ + 1)
      ≡⟨ cong (prefixLength e +_) (+-comm (suffixLength e′) _) ⟩
        prefixLength e + suc (suffixLength e′)
      ∎))
      (begin
        suc ((prefixLength e + suffixLength e′) + prefixLength (tail-⊆ e′))
      ≡⟨ cong (suc ∘ (_+ prefixLength (tail-⊆ {xs = suffix e} e′)) ∘ (prefixLength e +_))
          (suffixLength≡suffixLength-tail p e e′) ⟩
        suc ((prefixLength e + suffixLength (tail-⊆ {xs = suffix e} e′)) + prefixLength (tail-⊆ e′))
      ≡⟨ sym (length≡segmentLength e (tail-⊆ e′)) ⟩
        n
      ∎)
      (s≤s (+-mono-≤ (≤-refl {x = prefixLength e + suffixLength e′}) (0<prefixLength-tail e e′)))

shortenPath : ∀ {a b n} →
  Pathˡ a b n →
  n > size vertexFinite →
  Pathˡ< a b n
shortenPath p gt =
  uncurry (cutPathLoop p)
    (proj₂ (repeatElems (finitePigeonhole vertexFinite (trailˡ p) gt)))

shortEnoughPath : ∀ {a b n}
  (p : Pathˡ a b n) →
  Pathˡ≤ a b (size vertexFinite)
shortEnoughPath {n = n} p =
  case size vertexFinite <? n of λ where
    (yes m>v) → <-rec _ ind _ p m>v
    (no m≯v) → , ≮⇒≥ m≯v , p
  where
    ind = λ _ rec p gt →
      let m , le , q = shortenPath p gt in
        case size vertexFinite <? m of λ where
          (yes m>v) → rec _ le q m>v
          (no m≯v) → , ≮⇒≥ m≯v , q

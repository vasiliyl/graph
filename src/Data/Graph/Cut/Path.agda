open import Data.Graph

module Data.Graph.Cut.Path {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Graph.Cut.Vec
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as ×
open import Data.Sum as ⊎
open import Data.Vec hiding (_∷ʳ_)
open import Data.Vec.Any using (Any; here; there)
open import Data.Vec.Membership.Propositional
open import Finite
open import Finite.Pigeonhole
open import Function
open import Induction.Nat
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open FiniteGraph g
open IsFinite
open ≡-Reasoning

breakPath : ∀ {a b x l}
  (p : SizedPathˡ a b l)
  (e : x ∈ trailˡ p) →
  SizedPathˡ a x (prefixLength e) × SizedPathˡ x b (suc (suffixLength e))
breakPath [] ()
breakPath (e ∷ p) (here refl) = [] , e ∷ p
breakPath (e ∷ p) (there d) =
  let q , r = breakPath p d in
    e ∷ q , r

prefixPath : ∀ {a b x l}
  (p : SizedPathˡ a b l)
  (e : x ∈ trailˡ p) →
  SizedPathˡ a x _
prefixPath p = proj₁ ∘ breakPath p

suffixPath : ∀ {a b x l}
  (p : SizedPathˡ a b l)
  (e : x ∈ trailˡ p) →
  SizedPathˡ x b _
suffixPath p = proj₂ ∘ breakPath p

suffixLength≡suffixLength-tail : ∀ {a b x n}
  (p : SizedPathˡ a b n)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  suffixLength e′ ≡ suffixLength {xs = suffix e} (tail-⊆ e′)
suffixLength≡suffixLength-tail [] () e′
suffixLength≡suffixLength-tail (e ∷ p) (here refl) e′ = refl
suffixLength≡suffixLength-tail (e ∷ p) (there i) e′ = suffixLength≡suffixLength-tail p i e′

suffix≡suffixPath : ∀ {a b x l}
  (p : SizedPathˡ a b l)
  (e : x ∈ trailˡ p) →
  suffix e ≡ trailˡ (suffixPath p e)
suffix≡suffixPath [] ()
suffix≡suffixPath (e ∷ p) (here refl) = refl
suffix≡suffixPath (e ∷ p) (there i) = suffix≡suffixPath p i

segmentPath : ∀ {a b x l}
  (p : SizedPathˡ a b l)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  SizedPathˡ a x (prefixLength e) × SizedPathˡ x x (suc (prefixLength e′)) × SizedPathˡ x b (suc (suffixLength e′))
segmentPath p e e′ =
  let
    u , v = breakPath p e
    u′ , v′ = breakPath v (subst (_ ∈_) (suffix≡suffixPath p e) (tail-⊆ e′))
  in
    u ,
    subst (SizedPathˡ _ _) (prefixLengthLem p _ _) u′ ,
    subst (SizedPathˡ _ _) (cong suc (suffixLengthLem p _ _)) v′
  where
    prefixLengthLem : ∀ {a b x l}
      (p : SizedPathˡ a b l)
      (e : x ∈ trailˡ p)
      (e′ : x ∈ tail (suffix e)) →
      prefixLength (subst (_ ∈_) (suffix≡suffixPath p e) (tail-⊆ e′)) ≡ suc (prefixLength e′)
    prefixLengthLem [] () e′
    prefixLengthLem (e ∷ p) (here refl) e′ = refl
    prefixLengthLem (e ∷ p) (there i) e′ = prefixLengthLem p i e′

    suffixLengthLem : ∀ {a b x l}
      (p : SizedPathˡ a b l)
      (e : x ∈ trailˡ p)
      (e′ : x ∈ tail (suffix e)) →
      suffixLength (subst (_ ∈_) (suffix≡suffixPath p e) (tail-⊆ e′)) ≡ suffixLength e′
    suffixLengthLem [] () e′
    suffixLengthLem (e ∷ p) (here refl) e′ = refl
    suffixLengthLem (e ∷ p) (there i) e′′ = suffixLengthLem p i e′′

unbreak-≤ : ∀ {a b x n}
  (p : SizedPathˡ a b n)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  suc (prefixLength e) + suc (suffixLength e′) ≤ n
unbreak-≤ {n = n} p e e′ = subst₂ _≤_
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

cutPathLoop : ∀ {a b x n}
  (p : SizedPathˡ a b n)
  (e : x ∈ trailˡ p)
  (e′ : x ∈ tail (suffix e)) →
  Pathˡ< a b n
cutPathLoop {n = n} p e e′ = let u , v , w = segmentPath p e e′ in -, unbreak-≤ p e e′ , u ++ˡ w

cutRepeat : ∀ {a b n} →
  (p : SizedPathˡ a b n) → Repeats (trailˡ p) →
  Pathˡ< a b n
cutRepeat p r = let _ , e , e′ = repeatElems r in cutPathLoop p e e′

shortenPath : ∀ {a b n} →
  SizedPathˡ a b n →
  n > size vertexFinite →
  Pathˡ< a b n
shortenPath p gt =
  uncurry (cutPathLoop p)
    (proj₂ (repeatElems (finitePigeonhole vertexFinite (trailˡ p) gt)))

shortEnoughPath : ∀ {a b n}
  (p : SizedPathˡ a b n) →
  Pathˡ≤ a b (size vertexFinite)
shortEnoughPath {n = n} p =
  case size vertexFinite <? n of λ where
    (yes m>v) → <-rec _ ind _ p m>v
    (no m≯v) → -, ≮⇒≥ m≯v , p
  where
    ind = λ x rec p gt →
      let m , le , q = shortenPath p gt in
        case size vertexFinite <? m of λ where
          (yes m>v) → rec _ le q m>v
          (no m≯v) → -, ≮⇒≥ m≯v , q

acyclicPath : ∀ {a b n} →
  SizedPathˡ a b n →
  ∃ λ (p : Pathˡ≤ a b n) → ¬ Repeats (trailˡ (proj₂ (proj₂ p)))
acyclicPath {a} {b} {n} p =
  case repeats? decEqVertex (trailˡ p) of λ where
    (yes r) → <-rec Ind ind _ p ≤-refl r
    (no ¬r) → (-, ≤-refl , p) , ¬r
  where
    Ind = λ x →
      (p : SizedPathˡ a b x) → x ≤ n → Repeats (trailˡ p) →
      ∃ λ (p′ : Pathˡ≤ a b n) → ¬ Repeats (trailˡ (proj₂ (proj₂ p′)))

    ind = λ x rec p x≤n r →
      let
        y , y<x , p′ = cutRepeat p r
        _ , e , e′ = repeatElems r
      in
        case repeats? decEqVertex (trailˡ p′) of λ where
          (yes r′) → rec _ y<x _ (≤-trans (<⇒≤ (unbreak-≤ p e e′)) x≤n) r′
          (no ¬r′) → (-, ≤-trans (<⇒≤ y<x) x≤n , p′) , ¬r′

minimalPath : ∀ {a b n} →
  SizedPathˡ a b n →
  ∃ λ (p : Pathˡ≤ a b (size vertexFinite)) → ¬ Repeats (trailˡ (proj₂ (proj₂ p)))
minimalPath p =
  let
    x , x≤max , p′ = shortEnoughPath p
    (y , y≤x , p′′) , ¬r = acyclicPath p′
  in
    (y , ≤-trans y≤x x≤max , p′′) , ¬r

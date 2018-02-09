{-# OPTIONS --type-in-type #-}

module Graph.Cut.Vec where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product as ×
open import Data.Vec
open import Function
open import Pigeonhole
open import Relation.Binary.PropositionalEquality hiding ([_])

open ≡-Reasoning

loopStart : ∀ {A n} {xs : Vec A n} → Repeats xs → ∃ λ x → x ∈ xs
loopStart (here e) = , here
loopStart (there rs) = ×.map _ there (loopStart rs)

preLoop : ∀ {A n} {xs : Vec A n} → Repeats xs → Vec< A n
preLoop {xs = x ∷ xs} (here e) = , s≤s z≤n , []
preLoop {xs = x ∷ xs} (there rs) = ×.map _ (×.map s≤s (x ∷_)) (preLoop rs)

prefixLength : ∀ {A x l} {xs : Vec A l} → x ∈ xs → ℕ
prefixLength here = 0
prefixLength (there e) = suc (prefixLength e)

suffixLength : ∀ {A x l} {xs : Vec A l} → x ∈ xs → ℕ
suffixLength {l = suc l} here = l
suffixLength (there e) = suffixLength e

breakVec : ∀ {A x l} {xs : Vec A l}
  (e : x ∈ xs) →
  Vec A (suc (prefixLength e)) × Vec A (suc (suffixLength e))
breakVec {xs = x ∷ xs} here = [ x ] , x ∷ xs
breakVec {xs = x ∷ xs} (there e) = ×.map (x ∷_) id (breakVec e)

prefix : ∀ {A x l} {xs : Vec A l} (e : x ∈ xs) → Vec A _
prefix = proj₁ ∘ breakVec

suffix : ∀ {A x l} {xs : Vec A l} (e : x ∈ xs) → Vec A _
suffix = proj₂ ∘ breakVec

repeatElems : ∀ {A n} {xs : Vec A n} →
  Repeats xs →
  ∃₂ λ x (e : x ∈ xs) → x ∈ tail (suffix e)
repeatElems (here r) = , here , r
repeatElems (there rs) = ×.map _ (×.map there id) (repeatElems rs)

segmentVec : ∀ {A x l} {xs : Vec A l}
  (e : x ∈ xs)
  (e′ : x ∈ suffix e) →
  Vec A (suc (prefixLength e)) × Vec A (suc (prefixLength e′)) × Vec A (suc (suffixLength e′))
segmentVec e e′ = proj₁ (breakVec e) , breakVec e′

tail-⊆ : ∀ {A n} {xs : Vec A (suc n)} → tail xs ⊆V xs
tail-⊆ {xs = x ∷ xs} = there

length≡breakLength : ∀ {A x n} {xs : Vec A n}
  (e : x ∈ xs) →
  n ≡ suc (prefixLength e) + suffixLength e
length≡breakLength here = refl
length≡breakLength (there e) = cong suc (length≡breakLength e)

length≡segmentLength : ∀ {A x n} {xs : Vec A n}
  (e : x ∈ xs) →
  (e′ : x ∈ suffix e) →
  n ≡ suc (prefixLength e) + suffixLength e′ + prefixLength e′
length≡segmentLength {n = n} e e′ =
  begin
    n
  ≡⟨ length≡breakLength e ⟩
    suc (prefixLength e) + suffixLength e
  ≡⟨ sym (+-suc (prefixLength e) _) ⟩
    prefixLength e + suc (suffixLength e)
  ≡⟨ cong (prefixLength e +_) (length≡breakLength e′) ⟩
    prefixLength e + suc (prefixLength e′ + suffixLength e′)
  ≡⟨ +-suc (prefixLength e) _ ⟩
    suc (prefixLength e) + (prefixLength e′ + suffixLength e′)
  ≡⟨ cong (suc (prefixLength e) +_) (+-comm (prefixLength e′) _) ⟩
    suc (prefixLength e) + (suffixLength e′ + prefixLength e′)
  ≡⟨ sym (+-assoc (suc (prefixLength e)) _ _) ⟩
    (suc (prefixLength e) + suffixLength e′) + prefixLength e′
  ∎

0<prefixLength-tail : ∀ {A x n} {xs : Vec A n}
  (e : x ∈ xs)
  (e′ : x ∈ (tail (suffix e))) →
  0 < prefixLength {xs = suffix e} (tail-⊆ e′)
0<prefixLength-tail here e′ = s≤s z≤n
0<prefixLength-tail (there e) e′ = 0<prefixLength-tail e e′

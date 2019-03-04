open import Data.Graph

module Data.Graph.Path.Finite {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Category.Monad
open import Data.Bool as Bool
open import Data.Graph.Cut.Path g
open import Data.List as List hiding (_∷ʳ_)
open import Data.List.Any as Any
open import Data.List.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.List.Categorical as ListCat
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
open import Data.Product as Σ
open import Data.Unit using (⊤; tt)
open import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_)
import Level as ℓ
open import Finite
open import Finite.Pigeonhole
open import Function
open import Function.Equality using (Π)
open import Function.Equivalence using (Equivalence)
open import Function.Inverse using (Inverse)
open import Function.LeftInverse using (LeftInverse; leftInverse)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive hiding (_>>=_)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.HeterogeneousEquality as ≅
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation

open Π using (_⟨$⟩_)
open Equivalence using (to; from)
open FiniteGraph g
open Inverse using (to; from)
open IsFinite
open RawMonad {ℓᵥ ℓ.⊔ ℓₑ} ListCat.monad

isubst : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁}
  (A : I → Set ℓ₂) (B : ∀ {k} → A k → Set ℓ₃)
  {i j : I} {x : A i} {y : A j} →
  i ≡ j → x ≅ y →
  B x → B y
isubst A B refl refl = id

True-unique : ∀ {ℓ} {A : Set ℓ} (A? : Dec A) (x y : True A?) → x ≡ y
True-unique A? x y with A?
True-unique A? tt tt | yes a = refl
True-unique A? () y | no ¬a

True-unique-≅ : ∀
  {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  (A? : Dec A) (B? : Dec B)
  (x : True A?) (y : True B?) →
  x ≅ y
True-unique-≅ A? B? x y with A? | B?
True-unique-≅ A? B? tt tt | yes a | yes b = refl
True-unique-≅ A? B? x () | _ | no ¬b
True-unique-≅ A? B? () y | no ¬a | _

∃-≅ : ∀
  {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  {x y : A} {p : P x} {q : P y} →
  x ≡ y → p ≅ q → (∃ P ∋ (x , p)) ≡ (y , q)
∃-≅ refl refl = refl

nexts : ∀ {a b n} → Path a b n → List (∃ λ b → Path a b (suc n))
nexts {a} {b} p = List.map (λ where (_ , e) → -, p ∷ʳ e) (elements (edgeFinite b))

∈-nexts : ∀ {a c n} →
  (pf : IsFinite (∃ λ b → Path a b n)) →
  (p : Path a c (suc n)) →
  (c , p) ∈ (elements pf >>= (nexts ∘ proj₂))
∈-nexts pf p =
  case unsnoc p of λ where
    (_ , p′ , e′ , refl) →
      to >>=-∈↔ ⟨$⟩
        (-,
          membership pf (-, p′) ,
          ∈-map⁺ (membership (edgeFinite _) (-, e′)))

Path-finite : ∀ n a → IsFinite (∃ λ b → Path a b n)
Path-finite zero a = finite List.[ -, [] ] λ where (_ , []) → here refl
Path-finite (suc n) a =
  let pf = Path-finite n a in
    finite (elements pf >>= (nexts ∘ proj₂)) (∈-nexts pf ∘ proj₂)

≤-top? : ∀ {x y} → x ≤ suc y → x ≤ y ⊎ x ≡ suc y
≤-top? z≤n = inj₁ z≤n
≤-top? {y = zero} (s≤s z≤n) = inj₂ refl
≤-top? {y = suc y} (s≤s p) =
  case ≤-top? p of λ where
    (inj₁ le) → inj₁ (s≤s le)
    (inj₂ refl) → inj₂ refl

Path≤-finite : ∀ n a → IsFinite (∃ λ b → Path≤ a b n)
Path≤-finite zero a = finite List.[ -, -, z≤n , [] ] λ where (_ , _ , z≤n , []) → here refl
Path≤-finite (suc n) a =
  let
    finite xs elem = Path≤-finite n a
    finite xs′ elem′ = Path-finite (suc n) a
  in
    finite
      (List.map (Σ.map₂ (Σ.map₂ (Σ.map₁ ≤-step))) xs List.++
        List.map (Σ.map₂ (_,_ (suc n) ∘ _,_ ≤-refl)) xs′)
      λ where
        (b , m , le , p) → case ≤-top? le of λ where
          (inj₁ le′) →
            to ++↔ ⟨$⟩
              inj₁
                (to map-∈↔ ⟨$⟩
                  (-, (elem (b , m , le′ , p)) ,
                    ≡.cong (λ q → b , m , q , p) (≤-irrelevance le (≤-step le′))))
          (inj₂ refl) →
            to (++↔ {xs = List.map _ xs}) ⟨$⟩
              inj₂
                (to map-∈↔ ⟨$⟩
                  (-, elem′ (-, p) ,
                    ≡.cong (λ q → b , m , q , p) (≤-irrelevance le (s≤s ≤-refl))))

acyclic-length-≤ : ∀ {a b n} (p : Path a b n) → Acyclic (trail p) → n ≤ size vertexFinite
acyclic-length-≤ {n = n} p acp =
  case n ≤? size vertexFinite of λ where
    (yes le) → le
    (no ¬le) → contradiction (finitePigeonhole vertexFinite (trail p) (≰⇒> ¬le)) acp

AcyclicPath-finite : ∀
  a →
  IsFinite
    (∃₂ λ b n → ∃ λ (p : Path a b n) →
      True (acyclic? decEqVertex (trail p)))
AcyclicPath-finite a =
  via-left-inverse (IsFinite.filter (Path≤-finite (size vertexFinite) a) _) $
    leftInverse
      (λ where (b , n , p , acp) → (b , n , acyclic-length-≤ p (toWitness acp) , p) , acp)
      (λ where ((b , n , le , p) , acp) → b , n , p , acp)
      λ where _ → refl

AcyclicStar : Vertex → Vertex → Set _
AcyclicStar a b = ∃ λ (p : Star Edge a b) → True (acyclic? decEqVertex (starTrail p))

AcyclicStar-finite : ∀ a → IsFinite (∃ (AcyclicStar a))
AcyclicStar-finite a =
  via-left-inverse (AcyclicPath-finite a) $
    leftInverse
      (λ where
        (b , p , acp) →
          b , starLength p , fromStar p ,
            ≡.subst (True ∘ acyclic? decEqVertex) (trail-fromStar p) acp)
      (λ where
        (b , n , p , acp) →
          b , toStar p ,
            isubst (Vec Vertex) (True ∘ acyclic? decEqVertex)
              (starLength-toStar p) (starTrail-toStar p) acp)
      (λ where
        (b , p , acp) →
          ≡.cong (b ,_) $
            ∃-≅
              (≡.sym (toStar-fromStar p))
              (True-unique-≅ _ _ _ _))

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive
open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Category.Functor
open import Category.Monad
open import Category.Applicative
import Data.Maybe.Categorical as maybeCat

open import CoContextualPi.Linear.Types

module CoContextualPi.Linear.Multiplicities where

data Multiplicities : Set where
  unused once ω : Multiplicities

ExtUseCtx : ℕ → Set
ExtUseCtx n = Vec Multiplicities n

private
  variable
    n : ℕ
    m m₁ m₂ : Multiplicities
    Γ Γ₁ Γ₂ : ExtUseCtx n

upper-bound : Type n → Multiplicities
upper-bound (var _) = ω
upper-bound (#i _) = once
upper-bound (#o _) = once
upper-bound (_ ‵+ _) = ω
upper-bound (_ ‵× _) = ω
upper-bound ‵⊤ = ω

_+ₘ_ : Multiplicities → Multiplicities → Multiplicities
unused +ₘ m = m
once +ₘ unused = once
once +ₘ once = ω
once +ₘ ω = ω
ω +ₘ m = ω

data _≤ₘ_ : Multiplicities → Multiplicities → Set where
  reflex : m ≤ₘ m
  0≤1 : unused ≤ₘ once
  0≤ω : unused ≤ₘ ω
  1≤ω : once ≤ₘ ω

_≤ₘₗ_ : ExtUseCtx n → ExtUseCtx n → Set
_≤ₘₗ_ = Pointwise _≤ₘ_

≤ₘ-trans : m ≤ₘ m₁ → m₁ ≤ₘ m₂ → m ≤ₘ m₂
≤ₘ-trans reflex reflex = reflex
≤ₘ-trans 0≤1 reflex = 0≤1
≤ₘ-trans 0≤ω reflex = 0≤ω
≤ₘ-trans 1≤ω reflex = 1≤ω
≤ₘ-trans reflex 0≤1 = 0≤1
≤ₘ-trans reflex 0≤ω = 0≤ω
≤ₘ-trans reflex 1≤ω = 1≤ω
≤ₘ-trans 0≤1 1≤ω = 0≤ω

≤ₘₗ-trans : Γ ≤ₘₗ Γ₁ → Γ₁ ≤ₘₗ Γ₂ → Γ ≤ₘₗ Γ₂
≤ₘₗ-trans [] [] = []
≤ₘₗ-trans (x∼y ∷ le) (y∼z ∷ le1) = ≤ₘ-trans x∼y y∼z ∷ ≤ₘₗ-trans le le1  

VecOf : Multiplicities → ExtUseCtx n
VecOf {zero} _ = []
VecOf {suc n} m = m ∷ VecOf m

place_at_else_ : Multiplicities → Fin n → Multiplicities → ExtUseCtx n
place m at n else m' =  Vec.updateAt n (λ _ → m) (VecOf m')
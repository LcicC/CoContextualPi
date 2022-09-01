open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂)
open import Category.Functor
open import Category.Monad
open import Category.Applicative
open import Function using (_∘_)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])

import Data.Maybe.Categorical as maybeCat
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open import CoContextualPi.TypeSystem
open import CoContextualPi.Inference

module CoContextualPi.InferenceComplete where

iExp-comp : ∀(n m : ℕ)(e : Expr n)(t : Type m)(Γ : Ctx n m)
  → (pr : Γ ⊢ e ∶ t) → Σ[ m' ∈ ℕ ] Σ[ s ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ] Σ[ pr' ∈ Δ ⊢ e ∶ s ] 
  inferExpr e ≡ just (m' , s , Δ , pr') × (Σ[ σ ∈ (Fin m' → Type m) ] σ <| Δ ≡ Γ × σ <| s ≡ t)
iExp-comp n m .top .‵⊤ Γ top = _ , ‵⊤ , fresh , top , refl , {!   !} , {!   !} , refl
iExp-comp n m .(var _) t Γ (var x) = {!   !}
iExp-comp n m (fst e) t Γ (fst pr) =
  let aux = iExp-comp n m e _ Γ pr in
  let shape = var zero ‵× var (suc (zero {zero})) in
  let a = <[ t ] == [ shape ]> in
  {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !} , {!   !}
iExp-comp n m .(snd _) t Γ (snd pr) = {!   !}
iExp-comp n m .(inl _) .(_ ‵+ _) Γ (inl pr) = {!   !}
iExp-comp n m .(inr _) .(_ ‵+ _) Γ (inr pr) = {!   !}
iExp-comp n m .(_ ‵, _) .(_ ‵× _) Γ (pr ‵, pr₁) = {!   !}
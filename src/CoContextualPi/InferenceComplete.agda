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

-- If e is well-typed, inferExpr e returns just _
iExp-comp1 : ∀(n m : ℕ)(e : Expr n)(s : Type m)(Γ : Ctx n m) 
  → Γ ⊢ e ∶ s 
  → Σ[ m' ∈ ℕ ] Σ[ t ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ] Σ[ pr' ∈ Δ ⊢ e ∶ t ] inferExpr e ≡ just (m' , t , Δ , pr')
iExp-comp1 n m .top .‵⊤ Γ top = n , ‵⊤ , fresh , top , refl
iExp-comp1 n m .(var _) s Γ (var x) = n , Vec.lookup fresh _ , fresh , var refl , refl
iExp-comp1 n m (fst e) s Γ (fst prΓ) = {!   !} , {!   !} , {!   !} , {!   !} , {!   !} 
iExp-comp1 n m .(snd _) s Γ (snd prΓ) = {!   !}
iExp-comp1 n m .(inl _) .(_ ‵+ _) Γ (inl prΓ) = {!   !}
iExp-comp1 n m .(inr _) .(_ ‵+ _) Γ (inr prΓ) = {!   !}
iExp-comp1 n m .(_ ‵, _) .(_ ‵× _) Γ (prΓ ‵, prΓ₁) = {!   !}

-- inferExpr returns the most general solution
iExp-comp2 : ∀(n m : ℕ)(e : Expr n)(s : Type m)(Γ : Ctx n m)(pr : Γ ⊢ e ∶ s)
  → inferExpr e ≡ just (m , s , Γ , pr)
  → ∀ (m' : ℕ)(t : Type m')(Δ : Ctx n m') → Δ ⊢ e ∶ t
  → Σ[ σ ∈ (Fin m → Type m') ] σ <| Γ ≡ Δ × σ <| s ≡ t
iExp-comp2 n .n .top .‵⊤ .fresh top refl m' .‵⊤ Δ top = {!  !} , {!   !} , refl
iExp-comp2 n m .(var _) s Γ (var x) eq m' t Δ prΔ = {!   !}
iExp-comp2 n m .(fst _) s Γ (fst prΓ) eq m' t Δ prΔ = {!   !}
iExp-comp2 n m .(snd _) s Γ (snd prΓ) eq m' t Δ prΔ = {!   !}
iExp-comp2 n m .(inl _) .(_ ‵+ _) Γ (inl prΓ) eq m' t Δ prΔ = {!   !}
iExp-comp2 n m .(inr _) .(_ ‵+ _) Γ (inr prΓ) eq m' t Δ prΔ = {!   !}
iExp-comp2 n m .(_ ‵, _) .(_ ‵× _) Γ (prΓ ‵, prΓ₁) eq m' t Δ prΔ = {!   !}

iExp-comp : ∀(n m : ℕ)(e : Expr n)(t : Type m)(Γ : Ctx n m)
  → (pr : Γ ⊢ e ∶ t) → Σ[ m' ∈ ℕ ] Σ[ s ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ] Σ[ pr' ∈ Δ ⊢ e ∶ s ] 
  inferExpr e ≡ just (m' , s , Δ , pr') × (Σ[ σ ∈ (Fin m' → Type m) ] σ <| Δ ≡ Γ × σ <| s ≡ t)
iExp-comp n m e t Γ prΓ = 
  let m' , s , Δ , prΔ , eq = iExp-comp1 n m e t Γ prΓ in 
  let σ , eq1 , eq2 = iExp-comp2 n m' e s Δ prΔ eq m t Γ prΓ in 
  m' , s , Δ , prΔ , eq , σ , eq1 , eq2
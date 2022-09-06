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
  → Σ[ m' ∈ ℕ ] Σ[ t ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ] inferE e ≡ just (m' , t , Δ)
iExp-comp1 n m .top .‵⊤ Γ top = n , ‵⊤ , fresh , refl
iExp-comp1 n m (var x) s Γ (var pr-in) = n , Vec.lookup fresh x , fresh , refl
iExp-comp1 n m (fst e) s Γ (fst {t = s} {s = t} pr)  with iExp-comp1 n m e (s ‵× t) Γ pr
... | m' , t' , Δ , eqΔ = 
  let n' , σ , unify-eq , ext-eq = unify-complete {m = m' ℕ.+ 2} {l = m'} 
                <[ t' ] 
                [ var zero ‵× var (suc (zero {zero})) ]> 
                (sub (subst 
                        (λ x → Subst x m') 
                        (sym (trans (ℕₚ.+-suc m' 1) (cong suc (trans (ℕₚ.+-suc m' 0) (cong suc (ℕₚ.+-identityʳ m')))))) 
                        (([] -, zero ↦ {!   !}) -, suc zero ↦ {!   !})))
                {!   !} in
    {!   !}
-- comporre eqΔ e un-eq 

iExp-comp1 n m .(snd _) s Γ (snd pr) = {!   !}
iExp-comp1 n m .(inl _) .(_ ‵+ _) Γ (inl pr) = {!   !}
iExp-comp1 n m .(inr _) .(_ ‵+ _) Γ (inr pr) = {!   !}
iExp-comp1 n m .(_ ‵, _) .(_ ‵× _) Γ (pr ‵, pr₁) = {!   !}

-- inferExpr returns the most general solution
iExp-comp2 : ∀(n m : ℕ)(e : Expr n)(s : Type m)(Γ : Ctx n m)
  → inferE e ≡ just (m , s , Γ)
  → ∀ (m' : ℕ)(t : Type m')(Δ : Ctx n m') → Δ ⊢ e ∶ t
  → Σ[ σ ∈ (Fin m → Type m') ] σ <| Γ ≡ Δ × σ <| s ≡ t
iExp-comp2 n m e s Γ eq m' t Δ eqΔ = {!   !}

iExp-comp : ∀(n m : ℕ)(e : Expr n)(t : Type m)(Γ : Ctx n m)
  → (pr : Γ ⊢ e ∶ t) → Σ[ m' ∈ ℕ ] Σ[ s ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ]
  inferE e ≡ just (m' , s , Δ) × (Σ[ σ ∈ (Fin m' → Type m) ] σ <| Δ ≡ Γ × σ <| s ≡ t)
iExp-comp n m e t Γ prΓ = {!   !}
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

aux : ∀{n m} → (Fin m → Type n) → Fin (n ℕ.+ m) → Type n
aux {n} {zero}  f x = {!   !}
aux {zero} {suc m} f x = f x 
aux {suc n} {suc m} f zero  = var zero 
aux {suc n} {suc m} f (suc x) = {!   !}

-- If e is well-typed, inferExpr e returns just _
iExp-comp1 : ∀(n m : ℕ)(e : Expr n)(s : Type m)(Γ : Ctx n m) 
  → Γ ⊢ e ∶ s 
  → Σ[ m' ∈ ℕ ] Σ[ t ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ] inferE e ≡ just (m' , t , Δ)
iExp-comp1 n m .top .‵⊤ Γ top = n , ‵⊤ , fresh , refl
iExp-comp1 n m (var x) s Γ (var pr-in) = n , Vec.lookup fresh x , fresh , refl
iExp-comp1 n m (fst e) s Γ (fst {t = s} {s = t} pr)  with iExp-comp1 n m e (s ‵× t) Γ pr
... | m' , t' , Δ , eqΔ 
  with unify-complete {m = m' ℕ.+ 2} {l = m'} 
                <[ t' ] 
                [ var zero ‵× var (suc (zero {zero})) ]> 
                (aux {m'} {2} (λ{zero → {!  !} ; (suc zero) → {!   !}}))
                --(sub (subst 
                  --      (λ x → Subst x m') 
                    --    (sym (trans (ℕₚ.+-suc m' 1) (cong suc (trans (ℕₚ.+-suc m' 0) (cong suc (ℕₚ.+-identityʳ m')))))) 
                      --  (([] -, Fin.fromℕ m' ↦ {!   !}) -, Fin.fromℕ (suc m') ↦ {!   !})))
                {!  refl !} 
... | n' , σ , unify-eq , _ = n' , ([ var zero ]|> σ) , (σ <|[ Δ ]) , {!  !}
-- comporre eqΔ e un-eq 

iExp-comp1 n m .(snd _) s Γ (snd pr) = {!   !}
iExp-comp1 n m .(inl _) .(_ ‵+ _) Γ (inl pr) = {!   !}
iExp-comp1 n m .(inr _) .(_ ‵+ _) Γ (inr pr) = {!   !}
iExp-comp1 n m .(_ ‵, _) .(_ ‵× _) Γ (pr ‵, pr₁) = {!   !}

fresh-lookup-id : ∀{n m}(Γ : Ctx n m) → Vec.lookup Γ <| fresh ≡ Γ
fresh-lookup-id {zero} [] = refl
fresh-lookup-id {suc n} (x ∷ Γ) with fresh-lookup-id Γ
... | eq = cong (λ y → x ∷ y) (trans {!   !} eq)

fresh-lookup-var : ∀{n}(x : Fin n) → Vec.lookup fresh x ≡ var x
fresh-lookup-var {suc n} zero = refl
fresh-lookup-var {suc n} (suc x) with fresh-lookup-var x 
... | eq = {!   !}

iExp-comp : ∀(n m : ℕ)(e : Expr n)(s : Type m)(Γ : Ctx n m)
  → (pr : Γ ⊢ e ∶ s) 
  → Σ[ m' ∈ ℕ ] Σ[ t ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ]
      inferE e ≡ just (m' , t , Δ) × (Σ[ σ ∈ (Fin m' → Type m) ] σ <| Δ ≡ Γ × σ <| t ≡ s)
iExp-comp n m .top .‵⊤ Γ top  =
  n , ‵⊤ , fresh , refl , Vec.lookup Γ , fresh-lookup-id Γ , refl
iExp-comp n m (var x) .(Vec.lookup Γ x) Γ (var refl) = 
  n , Vec.lookup fresh x , fresh , refl , Vec.lookup Γ , fresh-lookup-id Γ , 
  subst (λ y → Vec.lookup Γ <| y ≡ Vec.lookup Γ x) (sym (fresh-lookup-var x)) refl
iExp-comp n m .(fst _) s Γ (fst prΓ) = {!   !}
iExp-comp n m .(snd _) s Γ (snd prΓ) = {!   !}
iExp-comp n m .(inl _) .(_ ‵+ _) Γ (inl prΓ) = {!   !}
iExp-comp n m .(inr _) .(_ ‵+ _) Γ (inr prΓ) = {!   !}
iExp-comp n m .(_ ‵, _) .(_ ‵× _) Γ (prΓ ‵, prΓ₁) = {!   !}
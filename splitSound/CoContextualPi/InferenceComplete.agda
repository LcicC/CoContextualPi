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
import Data.Maybe.Properties as Maybeₚ
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Properties as Vecₚ

open import CoContextualPi.Types
open import CoContextualPi.TypeSystem
open import CoContextualPi.Inference

module CoContextualPi.InferenceComplete where

fresh-lookup-id : ∀{n m}(Γ : Ctx n m) → Vec.lookup Γ <| fresh ≡ Γ
fresh-lookup-id {zero} [] = refl
fresh-lookup-id {suc n} (x ∷ Γ) with fresh-lookup-id Γ
... | eq = cong (λ y → x ∷ y) (trans {!   !} eq)

fresh-lookup-var : ∀{n}(x : Fin n) → Vec.lookup fresh x ≡ var x
fresh-lookup-var {suc n} zero = refl
fresh-lookup-var {suc n} (suc x) with fresh-lookup-var x 
... | eq = {!   !}

{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Completeness of Inference for Expressions %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-}

iExp-comp : ∀(n m : ℕ)(e : Expr n)(s : Type m)(Γ : Ctx n m)
  → (pr : Γ ⊢ e ∶ s) 
  → Σ[ m' ∈ ℕ ] Σ[ t ∈ Type m' ] Σ[ Δ ∈ Ctx n m' ]
      inferE e ≡ just (m' , t , Δ) × (Σ[ σ ∈ (Fin m' → Type m) ] σ <| Δ ≡ Γ × σ <| t ≡ s)
iExp-comp n m .top .‵⊤ Γ top  =
  n , ‵⊤ , fresh , refl , (Vec.lookup Γ , fresh-lookup-id Γ , refl)
iExp-comp n m (var x) .(Vec.lookup Γ x) Γ (var refl) = 
  n , Vec.lookup fresh x , fresh , refl , 
    (Vec.lookup Γ , fresh-lookup-id Γ , 
    subst (λ y → Vec.lookup Γ <| y ≡ Vec.lookup Γ x) (sym (fresh-lookup-var x)) refl)
iExp-comp n m (fst e) s Γ (fst {t = s} {s = t} prΓ)  
      with iExp-comp n m e (s ‵× t) Γ prΓ
... | m' , t' , Δ , inferE≡just , (σ , σΔ≡Γ , σt'≡s×t) rewrite inferE≡just
      with unify-complete {m = m' ℕ.+ 2} {l = m} 
                <[ t' ] [ var zero ‵× var (suc (zero {zero})) ]> 
                (merge σ λ{zero → s ; (suc zero) → t}) 
                (trans -- proof that unifies <[ t' ] [ var zero ‵× var (suc (zero {zero})) ]> 
                  (merge-eq-l σ _ t') 
                  (trans (trans σt'≡s×t refl) 
                    (sym (merge-eq-r σ _ (var zero ‵× var (suc (zero {zero})))))))
... | n' , σ' , unify≡just , (n'→m , ext-eq) rewrite unify≡just =
        let aux = (<|-≗ {n = m' ℕ.+ 2} {m} {f = merge σ _} {n'→m <> sub σ'} ext-eq) <[ Δ ] in
        n' , ([ var zero ]|> σ') , (σ' <|[ Δ ]) , 
        refl , 
        (n'→m , -- Substitution Fin n' → Type m
          trans (trans -- n'→m <| (σ' <|[ Δ ] ≡ Γ)
                  (<|-assoc n'→m (sub σ') <[ Δ ]) 
                  (trans (sym aux) (merge-eq-l σ _ Δ))
                ) σΔ≡Γ ,
          trans (sym (ext-eq _)) (merge-eq-r σ _ (var zero))) -- n'→m <| ([var zero]|> σ') ≡ s
iExp-comp n m .(snd _) s Γ (snd prΓ) = {!   !}
iExp-comp n m .(inl _) .(_ ‵+ _) Γ (inl prΓ) = {!   !}
iExp-comp n m .(inr _) .(_ ‵+ _) Γ (inr prΓ) = {!   !}
iExp-comp n m .(_ ‵, _) .(_ ‵× _) Γ (prΓ ‵, prΓ₁) = {!   !}  

{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Completeness of Inference for Processes %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-}


open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; subst; inspect; [_])
open import Relation.Nullary as ℝ using (Dec; yes; no; _because_; does)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

import Data.Nat.Properties as ℕₚ
import Data.Maybe.Properties as Maybeₚ

module CoContextualPi.Unification.Soundness (Name : ℕ → Set) (decEqName : ∀ {k} (x y : Name k) → Dec (x ≡ y)) where

open import CoContextualPi.Unification Name decEqName
open import CoContextualPi.Unification.Properties Name decEqName

private
  variable
    n m l k : ℕ
    u : Univ

flexFlex-sound : (x y : Fin m) {σ : Subst m n} → flexFlex x y ≡ (n , σ) → sub σ x ≡ sub σ y
flexFlex-sound {suc m} x y eq with thick x y | inspect (thick x) y
flexFlex-sound {suc m} x y refl | nothing | [ req ] = cong var (nothing-thick x y req)
flexFlex-sound {suc m} x y refl | just z | [ req ]
  with r , refl ← thick-reverse x y req
  rewrite thick-nothing x | thick-thin x r = cong var (sym (Maybeₚ.just-injective req))

flexRigid-sound : (x : Fin m) (t : Term m) {σ : Subst m n}
                  → flexRigid x t ≡ just (n , σ) → sub σ x ≡ sub σ <| t
flexRigid-sound {suc m} x t eq with check x t | inspect (check x) t
flexRigid-sound {suc m} x t refl | just t' | [ eq ]
  rewrite thick-nothing x | check-thin x t eq = begin
    (var <| t')
      ≡⟨ <|-≗ (λ y → cong (Maybe.maybe var t') (sym (thick-thin x y))) t' ⟩
    (Maybe.maybe var t' ∘ thick x ∘ thin x) <| t'
      ≡˘⟨ <|-assoc (Maybe.maybe var t' ∘ thick x) (|> (thin x)) t' ⟩
    (Maybe.maybe var t' ∘ thick x) <| (|> (thin x) <| t')
      ≡⟨ <|-≗ (λ t'' → sym (<|-id _)) (|> (thin x) <| t') ⟩
    ((var <|_) ∘ Maybe.maybe var t' ∘ thick x) <| (|> (thin x) <| t')
      ∎
    where open ≡.≡-Reasoning

amgu-sound : (s t : UTerm u m) (acc : ∃ (Subst m)) {σ : Subst m l}
           → amgu s t acc ≡ just (l , σ) → sub σ <| s ≡ sub σ <| t
amgu-sound {vec _} [] [] acc eq = refl
amgu-sound {vec _} (x ∷ xs) (y ∷ ys) (_ , acc) eq
  with just (_ , acc') ← amgu x y (_ , acc)
       | [ xyeq ] ← inspect (amgu x y) (_ , acc)
  with just (_ , acc'') ← amgu xs ys (_ , acc')
       | [ xsyseq ] ← inspect (amgu xs ys) (_ , acc')
  with xyf , refl ← amgu-acc x y acc xyeq
  with xsysf , refl ← amgu-acc xs ys acc' xsyseq
  with refl ← eq
  = cong₂ _∷_ helper (amgu-sound xs ys (_ , acc') xsyseq)
  where
    open ≡.≡-Reasoning
    helper : sub (xsysf ++ (xyf ++ acc)) <| x ≡ sub (xsysf ++ (xyf ++ acc)) <| y
    helper = begin
      sub (xsysf ++ (xyf ++ acc)) <| x
        ≡⟨ <|-≗ (sub-++ xsysf (xyf ++ acc)) x ⟩
      ((sub xsysf <|_) ∘ (sub (xyf ++ acc))) <| x
        ≡˘⟨ <|-assoc (sub xsysf) (sub (xyf ++ acc)) x ⟩
      sub xsysf <| ((sub (xyf ++ acc)) <| x)
        ≡⟨ cong (sub xsysf <|_) (amgu-sound x y (_ , acc) xyeq) ⟩
      sub xsysf <| ((sub (xyf ++ acc)) <| y)
        ≡⟨ <|-assoc (sub xsysf) (sub (xyf ++ acc)) y ⟩
      ((sub xsysf <|_) ∘ (sub (xyf ++ acc))) <| y
        ≡˘⟨ <|-≗ (sub-++ xsysf (xyf ++ acc)) y ⟩
      sub (xsysf ++ (xyf ++ acc)) <| y
        ∎

amgu-sound {one} (var x) (var y) (_ , []) eq = flexFlex-sound x y (Maybeₚ.just-injective eq)
amgu-sound {one} (var x) (con ny asy) (_ , []) eq = flexRigid-sound x (con ny asy) eq
amgu-sound {one} (con nx asx) (var y) (_ , []) eq = sym (flexRigid-sound y (con nx asx) eq)
amgu-sound {one} (con {kx} nx asx) (con {ky} ny asy) (_ , []) eq
  with yes refl ← kx ℕₚ.≟ ky
  with yes refl ← decEqName nx ny
  = cong (con nx) (amgu-sound asx asy idSubst eq)
amgu-sound {one} s t (_ , acc -, z ↦ r) eq
  rewrite amgu-step acc z r s t
  with just (_ , acc') ← amgu (r for z <| s) (r for z <| t) (_ , acc)
       | [ steq ] ← inspect (amgu (r for z <| s) (r for z <| t)) (_ , acc)
  with refl ← eq
  rewrite sym (<|-assoc (sub acc') (Maybe.maybe var r ∘ thick z) s)
  rewrite sym (<|-assoc (sub acc') (Maybe.maybe var r ∘ thick z) t)
  = amgu-sound (r for z <| s) (r for z <| t) (_ , acc) steq

unify-sound : (s t : UTerm u m) → Maybe (Σ[ l ∈ ℕ ] Σ[ σ ∈ Subst m l ] sub σ <| s ≡ sub σ <| t)
unify-sound s t with unify s t | inspect (unify s) t
unify-sound s t | nothing | _ = nothing
unify-sound s t | just (_ , σ) | [ eq ] = just (_ , σ , amgu-sound s t idSubst eq)
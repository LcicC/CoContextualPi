open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; subst; inspect; [_])
open import Relation.Nullary as ℝ using (Dec; yes; no; _because_; does)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Data.Nat.Properties as ℕₚ

module CoContextualPi.Unification.Completeness (Name : ℕ → Set) (decEqName : ∀ {k} (x y : Name k) → Dec (x ≡ y)) where

open import CoContextualPi.Unification Name decEqName
open import CoContextualPi.Unification.Properties Name decEqName

private
  variable
    n m l k : ℕ
    u : Univ
    
amgu-complete : ∀(s t : UTerm u m)(acc : Subst m n) 
  → (g : Fin n → Term l) → (g <> sub acc) <| s ≡ (g <> sub acc) <| t
  → Σ[ m' ∈ ℕ ] Σ[ f ∈ Subst m m' ] 
    (amgu s t (n , acc) ≡ just (m' , f) × Σ[ h ∈ (Fin m' → Term l) ] (g <> sub acc) ≗ (h <> sub f))

amgu-complete {u = one} {m = suc m} (var x) (var y) [] g eq with thick x y | inspect (thick x) y
... | nothing | [ th-eq ] rewrite nothing-thick x y th-eq = _ , [] , refl , g , λ _ → refl
... | just z | [ th-eq ] = _ , ([] -, x ↦ var z) , refl , g ∘ thin x , λ xx → check-eq xx
    where
      check-eq : ∀ xx → g xx ≡ (g ∘ (thin x)) <| (var <> ((var z) for x)) xx
      check-eq xx with thick x xx | inspect (thick x) xx
      check-eq xx | nothing | [ e ]
        rewrite <|-id (var z) rewrite sym (nothing-thick x xx e) = trans eq (cong g (thin-thick x y z th-eq))
      check-eq xx | just z' | [ e ] = cong g (thin-thick x xx z' e)
amgu-complete {u = one} {m = suc m} (var x) (con ny ys) [] g eq with check x (con ny ys) | inspect (check x) (con ny ys)
... | just t' | [ ch-eq ] = 
  m , [] -, x ↦ t' , refl , g ∘ (thin x) , λ z → check-eq z
    where
      check-eq : ∀ z → g z ≡ (g ∘ (thin x)) <| (var <> (t' for x)) z 
      check-eq z with thick x z | inspect (thick x) z
      check-eq z | nothing | [ e ] 
        rewrite <|-id t' rewrite sym (nothing-thick x z e) = 
        let ch-th-eq = check-thin x (con ny ys) ch-eq in
        trans eq (trans (cong (_<|_ g) ch-th-eq) (<|-assoc g (|> (thin x)) t'))
      check-eq z | just z' | [ e ] = cong g (thin-thick x z z' e)
... | nothing | [ ch-eq ] = ⊥-elim (check-⊥ x ys ny g eq ch-eq)
amgu-complete {u = one} {m = suc m} (con nx xs) (var y) [] g eq with check y (con nx xs) | inspect (check y) (con nx xs)
... | just t' | [ ch-eq ] = 
  m , [] -, y ↦ t' , refl , g ∘ thin y , λ z → check-eq z
    where
      check-eq : ∀ z → g z ≡ (g ∘ (thin y)) <| (var <> (t' for y)) z 
      check-eq z with thick y z | inspect (thick y) z
      check-eq z | nothing | [ e ] 
        rewrite <|-id t' rewrite sym (nothing-thick y z e) = 
        let ch-th-eq = check-thin y (con nx xs) ch-eq in
        trans (sym eq) (trans (cong (_<|_ g) ch-th-eq) (<|-assoc g (|> (thin y)) t'))
      check-eq z | just z' | [ e ] = cong g (thin-thick y z z' e)
... | nothing | [ ch-eq ] = ⊥-elim (check-⊥ y xs nx g (sym eq) ch-eq)
amgu-complete {u = one} (con {kx} nx xs) (con {ky} ny ys) acc g eq with kx ℕₚ.≟ ky
... | no ¬eq = ⊥-elim (¬eq (con-arity-eq kx ky eq))
... | yes refl with decEqName nx ny
...   | no ¬eq = ⊥-elim (¬eq (con-name-eq nx ny eq))
...   | yes refl = 
          amgu-complete xs ys acc g (con-args-eq ((g <> sub acc) <| xs) ((g <> sub acc) <| ys) eq)
amgu-complete {u = one} s t (acc -, z ↦ r) g eq
  rewrite sym (<|-≗ (<>-assoc g (sub acc) (r for z)) s)
  rewrite sym (<|-≗ (<>-assoc g (sub acc) (r for z)) t)
  rewrite sym (<|-assoc (g <> sub acc) (r for z) s)
  rewrite sym (<|-assoc (g <> sub acc) (r for z) t)
  with m1 , f1 , eq1 , h1 , exteq1 ← amgu-complete ((r for z) <| s) ((r for z) <| t) acc g eq = 
  let amgu-eq = amgu-singleSubst {!  s !} t {!   !} r z {!   !} eq1 in
  m1 , (f1 ++ ([] -, z ↦ r)) , amgu-eq , h1 , {!   !}
amgu-complete {u = vec _} [] [] acc g eq = _ , acc , refl , g , λ _ → refl
amgu-complete {u = vec _} (x ∷ xs) (y ∷ ys) acc g eq 
  -- amgu first computed con the heads
  with 
    m1 , f1 , eq1 , h1 , exteq1 ← amgu-complete x y acc g (cong Vec.head eq) | 
    eq-xs-ys ← cong Vec.tail eq
  rewrite eq1
  -- obtain <| equalities from extensional equality
  with 
    eq-xs ← (<|-≗ {f = g <> sub acc}{h1 <> sub f1} exteq1) xs | 
    eq-ys ← (<|-≗ {f = g <> sub acc}{h1 <> sub f1} exteq1) ys
  -- amgu computed with updated accumulator
  with
    m2 , f2 , eq2 , h2 , exteq2 ← amgu-complete xs ys f1 h1 (trans (sym eq-xs) (trans eq-xs-ys eq-ys)) = 
    m2 , f2 , eq2 , h2 , λ z → trans (exteq1 z) (exteq2 z)


unify-complete : ∀(s t : UTerm u m) (g : Fin m → Term l) → g <| s ≡ g <| t 
  → Σ[ n ∈ ℕ ] Σ[ f ∈ Subst m n ](unify s t ≡ just (n , f) × Σ[ h ∈ (Fin n → Term l) ](g ≗ h <> sub f))
unify-complete s t g eq = amgu-complete s t [] g eq  
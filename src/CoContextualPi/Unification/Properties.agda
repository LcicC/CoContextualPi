open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; subst; inspect; [_])
open import Relation.Nullary as ℝ using (Dec; yes; no; _because_; does)

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _⊔_; _≤_; z≤n; s≤s)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ

module CoContextualPi.Unification.Properties (Name : ℕ → Set) (decEqName : ∀ {k} (x y : Name k) → Dec (x ≡ y)) where

open import CoContextualPi.Unification Name decEqName

private
  variable
    n m l k : ℕ
    u : Univ

{- Maybe & Fin absurds -}

maybe-abs : ∀{l}{A : Set l}{t : A} → nothing ≡ just t → ⊥
maybe-abs ()

fin-abs : ∀{i : Fin m} → zero ≡ (Fin.suc i) → ⊥
fin-abs ()

----------------------

-- This must be in the stdlib somewhere?
infix 15 _≗_
_≗_ : {A : Set} {B : Set} → (A → B) → (A → B) → Set
f ≗ g = ∀ x → f x ≡ g x

<|-id : (t : UTerm u n) → var <| t ≡ t
<|-id {u = one} (var x) = refl
<|-id {u = one} (con n as) = cong (con n) (<|-id as)
<|-id {u = vec _} [] = refl
<|-id {u = vec _} (x ∷ xs) = cong₂ _∷_ (<|-id x) (<|-id xs)

<|-assoc : (f : Fin m → Term n) (g : Fin l → Term m) (t : UTerm u l) → f <| (g <| t) ≡ (f <> g) <| t
<|-assoc {u = one} f g (var x) = refl
<|-assoc {u = one} f g (con n as) = cong (con n) (<|-assoc f g as)
<|-assoc {u = vec _} f g [] = refl
<|-assoc {u = vec _} f g (x ∷ xs) = cong₂ _∷_ (<|-assoc f g x) (<|-assoc f g xs)

<|-≗ : {f g : Fin n → Term m} → f ≗ g → (_<|_ {u = u} f) ≗ (_<|_ {u = u} g)
<|-≗ {u = one} eq (var x) = eq x
<|-≗ {u = one} eq (con n as) = cong (con n) (<|-≗ eq as)
<|-≗ {u = vec _} eq [] = refl
<|-≗ {u = vec _} eq (x ∷ xs) = cong₂ _∷_ (<|-≗ eq x) (<|-≗ eq xs)

thick-nothing : (x : Fin (suc n)) → thick x x ≡ nothing
thick-nothing zero = refl
thick-nothing {suc n} (suc x) rewrite thick-nothing x = refl
  
thick-reverse : ∀ (x y : Fin (suc n)) {r : Fin n} → thick x y ≡ just r → ∃[ y' ] (y ≡ thin x y')
thick-reverse zero (suc y) eq = y , refl
thick-reverse {suc n} (suc x) zero refl = zero , refl
thick-reverse {suc n} (suc x) (suc y) {zero} eq with thick x y
thick-reverse {suc n} (suc x) (suc y) {zero} () | nothing
thick-reverse {suc n} (suc x) (suc y) {zero} () | just _
thick-reverse {suc n} (suc x) (suc y) {suc r} eq =
  Product.map suc (cong suc) (thick-reverse x y (Maybeₚ.map-injective Finₚ.suc-injective eq))

nothing-thick : (x y : Fin (suc n)) → thick x y ≡ nothing → x ≡ y
nothing-thick zero zero eq = refl
nothing-thick {suc n} (suc x) (suc y) eq =
  cong suc (nothing-thick x y (Maybeₚ.map-injective Finₚ.suc-injective eq))

thick-thin : (x : Fin (suc n)) (y : Fin n) → thick x (thin x y) ≡ just y
thick-thin zero y = refl
thick-thin (suc x) zero = refl
thick-thin (suc x) (suc y) = cong (Maybe.map suc) (thick-thin x y)

thick-res : ∀(x y : Fin (suc m)) → thick (suc x) (suc y) ≡ nothing ⊎ Σ[ z ∈ Fin m ] thick (suc x) (suc y) ≡ just (suc z)
thick-res {m = zero} zero zero = inj₁ refl
thick-res {m = suc m} zero zero = inj₁ refl
thick-res {m = suc m} zero (suc y) = inj₂ (y , refl)
thick-res {m = suc m} (suc x) zero = inj₂ (zero , refl)
thick-res {m = suc m} (suc x) (suc y) with thick-res x y 
... | inj₁ e rewrite e = inj₁ refl
... | inj₂ (z , e) rewrite e = inj₂ (suc z , refl)

thick-suc : ∀(x y : Fin (suc m))(z : Fin m) → thick (suc x) (suc y) ≡ just (suc z) → thick x y ≡ just z
thick-suc {m = m} x y z eq with thick x y | inspect (thick x) y
thick-suc {m = m} x y z () | nothing | [ _ ]
... | just z' | [ e ] = 
  let eq1 = Finₚ.suc-injective (Maybeₚ.just-injective eq) in cong just eq1
 
thin-thick : ∀(x y : Fin (suc m))(z : Fin m) → thick x y ≡ just z → y ≡ thin x z
thin-thick zero (suc .z) z refl = refl
thin-thick (suc _) zero zero refl = refl
thin-thick {suc m} (suc x) (suc y) zero eq with thick-res x y
... | inj₁ e rewrite e = ⊥-elim (maybe-abs eq)
... | inj₂ (z , e) rewrite e = ⊥-elim (fin-abs (sym (Maybeₚ.just-injective eq)))
thin-thick {suc m} (suc x) (suc y) (suc z) eq = cong suc (thin-thick x y z (thick-suc x y z eq))

check-thin : (i : Fin (suc n)) (t : UTerm u (suc n)) {t' : UTerm u n}
           → check i t ≡ just t' → t ≡ |> (thin i) <| t'
check-thin {u = one} i (var x) eq
  with just y ← thick i x | [ qe ] ← inspect (thick i) x
  with refl ← eq
  with y' , refl ← thick-reverse i x qe
  rewrite thick-thin i y'
  with refl ← qe
  = refl
check-thin {u = one} i (con n as) eq
  with just y ← check i as | [ qe ] ← inspect (check i) as
  with refl ← eq
  = cong (con n) (check-thin i as qe)
check-thin {u = vec _} i [] refl = refl
check-thin {u = vec _} i (x ∷ xs) eq
  with just y ← check i x | [ qe ] ← inspect (check i) x
  with just ys ← check i xs | [ qes ] ← inspect (check i) xs
  with refl ← eq
  = cong₂ _∷_ (check-thin i x qe) (check-thin i xs qes)


sub-++ : (xs : Subst m n) (ys : Subst l m) → sub (xs ++ ys) ≗ sub xs <> sub ys
sub-++ xs [] t = refl
sub-++ xs (ys -, i ↦ t') t
  rewrite <|-assoc {u = one} (sub xs) (sub ys) (Maybe.maybe var t' (thick i t))
  = <|-≗ (sub-++ xs ys) (Maybe.maybe var t' (thick i t))

++-id : (xs : Subst m n) → [] ++ xs ≡ xs
++-id [] = refl
++-id (xs -, z ↦ r) = cong (_-, z ↦ r) (++-id xs)

++-assoc : (xs : Subst m n) (ys : Subst l m) (zs : Subst k l) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc xs ys [] = refl
++-assoc xs ys (zs -, z ↦ r) = cong (_-, z ↦ r) (++-assoc xs ys zs)

{- Constructors equalities -}

con-name-eq : ∀(nx ny : Name k){xs ys : Vec (Term m) k} → con nx xs ≡ con ny ys → nx ≡ ny
con-name-eq nx .nx refl = refl

con-arity-eq : ∀ (kx ky : ℕ) {nx : Name kx}{ny : Name ky}{xs : Vec (Term m) kx}{ys : Vec (Term m) ky} 
  → con {k = kx} nx xs ≡ con {k = ky} ny ys → kx ≡ ky
con-arity-eq kx .kx refl = refl

con-args-eq : ∀{nx ny : Name k}(xs ys : Vec (Term m) k) → con nx xs ≡ con ny ys → xs ≡ ys
con-args-eq xs .xs refl = refl

{- ##### If I have a unifier ⇒ check must not fail ##### -}
{- Thanks @Francesco Dagnino for the contribution -}

-- Used in Unification.Completeness in amgu-complete
-- _⊔_ computes the maximum

check-nothing : (x y : Fin (suc n)) → check x (var y) ≡ nothing → thick x y ≡ nothing
check-nothing x y eq = Maybeₚ.map-injective var-injective eq

check-vec : (x : Fin (suc n)) (t : Term (suc n)) (v : Vec (Term (suc n)) k)
            → check x (t ∷ v) ≡ nothing → check x t ≡ nothing ⊎ check x v ≡ nothing
check-vec x t v eq with check x t
... | nothing = inj₁ refl
... | just s  with check x v
...           | nothing = inj₂ refl
...           | just w  = ⊥-elim (maybe-abs (sym eq))

-- height of a term
ht : UTerm u n → ℕ
ht {u = one} (var _) = zero
ht {u = one} (con _ v) = suc (ht v)
ht {u = vec _} [] = zero
ht {u = vec _} (t ∷ v) = (ht t) ⊔ (ht v)

ht-sub : (x : Fin (suc n)) (t : UTerm u (suc n)) (g : Fin (suc n) → Term m)
          → check x t ≡ nothing
          → ht (g x) ≤ ht (g <| t)
ht-sub {u = one} x (var y) g ch≡n =
    ℕₚ.≤-reflexive (cong (ht ∘ g) (nothing-thick x y (check-nothing x y ch≡n)))
ht-sub {u = one} x (con c v) g ch≡n =
    let gx≤gv = ht-sub x v g (Maybeₚ.map-injective args-injective ch≡n) in
    ℕₚ.≤-trans (ℕₚ.n≤1+n _) (s≤s gx≤gv)
ht-sub {u = vec .(suc _)} x (t ∷ v) g ch≡n with check-vec x t v ch≡n
... | inj₁ eqt = ℕₚ.m≤n⇒m≤n⊔o _ (ht-sub x t g eqt)
... | inj₂ eqv = ℕₚ.m≤n⇒m≤o⊔n _ (ht-sub x v g eqv)

check-⊥ : (x : Fin (suc n)) (v : Vec (Term (suc n)) k) → ∀ c → (g : Fin (suc n) → Term m)
          → g <| (var x) ≡ g <| (con c v) → check x (con c v) ≡ nothing
          → ⊥
check-⊥ x v c g gx≡con ch≡n =
    ℕₚ.1+n≰n {n = ht (g x)}
        (ℕₚ.≤-trans (s≤s (ht-sub x v g (Maybeₚ.map-injective args-injective ch≡n)))
                      (ℕₚ.≤-reflexive (cong ht (sym gx≡con))))
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl; _≢_; trans; cong; cong₂; sym; subst; inspect; [_])
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary as ℝ using (Dec; yes; no; _because_; does)
open import Relation.Nullary.Decidable as Dec using ()

open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (∃; Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Bool
open import Data.Empty
open import Data.Sum

import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Maybe.Properties as Maybeₚ
import Data.Product.Properties as Productₚ
import Data.Vec.Properties as Vecₚ

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

amgu-step : (acc : Subst m n) (z : Fin (suc m)) (r : Term m) (s t : UTerm u (suc m))
          → amgu s t (_ , acc -, z ↦ r)
          ≡ Maybe.map (Product.map₂ (_-, z ↦ r)) (amgu (r for z <| s) (r for z <| t) (_ , acc))
amgu-step {u = one} acc z r (var x) (var y) = refl
amgu-step {u = one} acc z r (var x) (con ny asy) = refl
amgu-step {u = one} acc z r (con nx asx) (var y) = refl
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) with kx ℕₚ.≟ ky
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | no kx≢ky = refl
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | yes refl with decEqName nx ny
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | yes refl | no nx≢ny = refl
amgu-step {u = one} acc z r (con {kx} nx asx) (con {ky} ny asy) | yes refl | yes refl = amgu-step acc z r asx asy
amgu-step {u = vec _} acc z r [] [] = refl
amgu-step {u = vec _} acc z r (x ∷ xs) (y ∷ ys)
    with amgu (r for z <| x) (r for z <| y) (_ , acc)
       | inspect (amgu (r for z <| x) (r for z <| y)) (_ , acc)
... | nothing | [ eq ] rewrite amgu-step acc z r x y | eq = refl
... | just (_ , acc') | [ eq ]
      with amgu (r for z <| xs) (r for z <| ys) (_ , acc')
        | inspect (amgu (r for z <| xs) (r for z <| ys)) (_ , acc')
...   | nothing | [ qe ] rewrite amgu-step acc z r x y | eq | amgu-step acc' z r xs ys | qe = refl
...   | just (_ , acc'') | [ qe ] rewrite amgu-step acc z r x y | eq | amgu-step acc' z r xs ys | qe = refl


amgu-acc : (s t : UTerm u m) (acc : Subst m n) {σ : Subst m l}
         → amgu s t (_ , acc) ≡ just (l , σ)
         → ∃[ found ] (σ ≡ found ++ acc)
amgu-acc {vec _} [] [] acc refl = _ , sym (++-id _)
amgu-acc {vec _} (x ∷ xs) (y ∷ ys) acc eq
  with just (_ , acc') ← amgu x y (_ , acc)
       | [ xyeq ] ← inspect (amgu x y) (_ , acc)
  with just (_ , acc'') ← amgu xs ys (_ , acc')
       | [ xsyseq ] ← inspect (amgu xs ys) (_ , acc')
  with _ , refl ← amgu-acc x y acc xyeq
  with _ , refl ← amgu-acc xs ys acc' xsyseq
  with refl ← eq
  = _ , sym (++-assoc _ _ acc)
amgu-acc {one} (var x) (var y) [] eq = _ , refl
amgu-acc {one} (var x) (con ny asy) [] eq = _ , refl
amgu-acc {one} (con nx asx) (var y) [] eq = _ , refl
amgu-acc {one} (con {kx} nx asx) (con {ky} ny asy) [] eq = _ , refl
amgu-acc {one} s t (acc -, z ↦ r) eq
  rewrite amgu-step acc z r s t
  with just (_ , acc') ← amgu (r for z <| s) (r for z <| t) (_ , acc)
       | [ steq ] ← inspect (amgu (r for z <| s) (r for z <| t)) (_ , acc)
  with refl ← eq
  with _ , refl ← amgu-acc (r for z <| s) (r for z <| t) acc steq
  = _ , refl


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

{- ########## Completeness ########## -}

{- Constructors equalities -}

con-name-eq : ∀(nx ny : Name k){xs ys : Vec (Term m) k} → con nx xs ≡ con ny ys → nx ≡ ny
con-name-eq nx .nx refl = refl

con-arity-eq : ∀ (kx ky : ℕ) {nx : Name kx}{ny : Name ky}{xs : Vec (Term m) kx}{ys : Vec (Term m) ky} 
  → con {k = kx} nx xs ≡ con {k = ky} ny ys → kx ≡ ky
con-arity-eq kx .kx refl = refl

con-args-eq : ∀{nx ny : Name k}(xs ys : Vec (Term m) k) → con nx xs ≡ con ny ys → xs ≡ ys
con-args-eq xs .xs refl = refl

---------------------

uf-comp : ∀(s t : UTerm u m)(acc : Subst m n) 
  → (g : Fin n → Term l) → (g <> sub acc) <| s ≡ (g <> sub acc) <| t
  → Σ[ m' ∈ ℕ ] Σ[ f ∈ Subst m m' ] 
    (amgu s t (n , acc) ≡ just (m' , f) × Σ[ h ∈ (Fin m' → Term l) ] (g <> sub acc) ≗ (h <> sub f))

uf-comp {u = one} {m = suc m} (var x) (var y) [] g eq with thick x y | inspect (thick x) y
... | nothing | [ th-eq ] rewrite nothing-thick x y th-eq = _ , [] , refl , g , λ _ → refl
... | just z | [ th-eq ] = _ , ([] -, x ↦ var z) , refl , g ∘ thin x , λ xx → check-eq xx
    where
      check-eq : ∀ xx → g xx ≡ (g ∘ (thin x)) <| (var <> ((var z) for x)) xx
      check-eq xx with thick x xx | inspect (thick x) xx
      check-eq xx | nothing | [ e ]
        rewrite <|-id (var z) rewrite sym (nothing-thick x xx e) = trans eq (cong g (thin-thick x y z th-eq))
      check-eq xx | just z' | [ e ] = cong g (thin-thick x xx z' e)
uf-comp {u = one} {m = suc m} (var x) (con ny ys) [] g eq with check x (con ny ys) | inspect (check x) (con ny ys)
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
... | nothing | [ ch-eq ] = {!  !} -- absurd
uf-comp {u = one} {m = suc m} (con nx xs) (var y) [] g eq with check y (con nx xs) | inspect (check y) (con nx xs)
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
... | nothing | [ eq ] = {!   !} -- absurd
uf-comp {u = one} (con {kx} nx xs) (con {ky} ny ys) acc g eq with kx ℕₚ.≟ ky
... | no ¬eq = ⊥-elim (¬eq (con-arity-eq kx ky eq))
... | yes refl with decEqName nx ny
...   | no ¬eq = ⊥-elim (¬eq (con-name-eq nx ny eq))
...   | yes refl = 
          uf-comp xs ys acc g (con-args-eq ((g <> sub acc) <| xs) ((g <> sub acc) <| ys) eq)
uf-comp {u = one} s t (acc -, z ↦ r) g eq
  -- rewrite <|-≗ (sub-++ acc ([] -, z ↦ r)) s 
  rewrite sym (<|-assoc g (sub acc) ((r for z) <| s)) =
  -- with eq-assoc ← <|-assoc g (sub (acc -, z ↦ r)) s =
  let rec = uf-comp ((r for z) <| s) ((r for z) <| t) acc {!   !} {!   !} in {!   !}
uf-comp {u = vec _} [] [] acc g eq = _ , acc , refl , g , λ _ → refl
uf-comp {u = vec _} (x ∷ xs) (y ∷ ys) acc g eq 
  -- amgu first computed con the heads
  with 
    m1 , f1 , eq1 , h1 , exteq1 ← uf-comp x y acc g (cong Vec.head eq) | 
    eq-xs-ys ← cong Vec.tail eq
  rewrite eq1
  -- obtain <| equalities from extensional equality
  with 
    eq-xs ← (<|-≗ {f = g <> sub acc}{h1 <> sub f1} exteq1) xs | 
    eq-ys ← (<|-≗ {f = g <> sub acc}{h1 <> sub f1} exteq1) ys
  -- amgu computed with updated accumulator
  with
    m2 , f2 , eq2 , h2 , exteq2 ← uf-comp xs ys f1 h1 (trans (sym eq-xs) (trans eq-xs-ys eq-ys)) = 
    m2 , f2 , eq2 , h2 , λ z → trans (exteq1 z) (exteq2 z)


ufc : ∀(s t : UTerm u m) (g : Fin m → Term l) → g <| s ≡ g <| t 
  → Σ[ n ∈ ℕ ] Σ[ f ∈ Subst m n ](unify s t ≡ just (n , f) × Σ[ h ∈ (Fin n → Term l) ](g ≗ h <> sub f))
ufc s t g eq = uf-comp s t [] g eq       
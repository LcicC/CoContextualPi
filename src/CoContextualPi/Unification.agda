open import Function using (_∘_)

open import Data.Maybe as Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product as Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)


open import CoContextualPi.Types

module CoContextualPi.Unification where


private
  variable
    n m l : ℕ


-- Occurs check, lowers the term if the variable is not present
check : Fin (suc n) → Type (suc n) → Maybe (Type n)
check x (′ y) = Maybe.map ′_ (thick x y)
check x top = just top
check x (# t) = Maybe.map #_ (check x t)
check x < t₁ , t₂ > = Maybe.ap (Maybe.map <_,_> (check x t₁)) (check x t₂)


-- Substitutions from variable x to variable y
flexFlex : Fin m → Fin m → Σ ℕ (AList m)
flexFlex {suc m} x y = Maybe.maybe (λ y' → _ , [] -, x ↦ ′ y') (_ , []) (thick x y)


-- Substitutions from variable x to term t
flexRigid : Fin m → Type m → Maybe (Σ ℕ (AList m))
flexRigid {suc m} x t = Maybe.map (λ t' → _ , ([] -, x ↦ t')) (check x t)


-- Unification with the aid of an accumulator
amgu : Type m → Type m → AList m n → Maybe(Σ ℕ (AList m))

-- Base case and inductive cases
amgu top top acc = just (_ , acc)
amgu (# s) (# t) acc = amgu s t acc
amgu < lx , rx > < ly , ry > acc = amgu lx ly acc Maybe.>>= amgu rx ry ∘ proj₂

-- Mismatches
amgu top (# t) acc = nothing
amgu (# s) top acc = nothing
amgu top < l , r > acc = nothing
amgu < l , r > top acc = nothing
amgu (# s) < l , r > acc = nothing
amgu < l , r > (# t) acc = nothing

-- New substitutions found
amgu (′ x) (′ y) [] = just (flexFlex x y)
amgu (′ x) t [] = flexRigid x t
amgu s (′ x) [] = flexRigid x s

-- Apply existing substitutions
amgu s t (acc -, z ↦ r) = Maybe.map (Product.map₂ (_-, (z ↦ r)))
                                    (amgu (r for z <| s) (r for z <| t) acc)



-- Lift everything to typing contexts

[_]⇓ : (Fin m → Type l) → Vec (Type m) n → Vec (Type l) n
[ σ ]⇓ = Vec.map (σ <|_)

amgus : Vec (Type m) n → Vec (Type m) n → AList m l → Maybe (Σ ℕ (AList m))
amgus [] [] acc = just (_ , acc)
amgus (x ∷ xs) (y ∷ ys) acc = do _ , acc' ← amgu x y acc
                                 amgus xs ys acc'

unify : Vec (Type m) n → Vec (Type m) n → Maybe (Σ ℕ (AList m))
unify xs ys = amgus xs ys []

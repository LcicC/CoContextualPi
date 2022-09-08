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

module CoContextualPi.Inference where

private
  variable
    n m l k : ℕ
    u v : Univ

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative


fresh : Ctx n n
fresh {n = zero} = []
fresh {n = suc n} = var zero ∷ Vec.map ((|> suc) <|_) fresh

infixr 2 !_
pattern !_ t = _ , t


<|-lookup : (σ : Fin m → Type l) (xs : Vec (Type m) n) {i : Fin n}
          → Vec.lookup (σ <| xs) i ≡ σ <| (Vec.lookup xs i)
<|-lookup σ (x ∷ xs) {zero} = refl
<|-lookup σ (x ∷ xs) {suc i} = <|-lookup σ xs

<|-∋ : (σ : Fin m → Type l) (xs : Vec (Type m) n) {x : Fin n} {t : Type m}
     → xs ∋ x ∶ t → (σ <| xs) ∋ x ∶ (σ <| t)
<|-∋ σ xs refl = <|-lookup σ xs

<|-⊢-∶ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {e : Expr n} {t : Type m}
       → xs ⊢ e ∶ t → (σ <| xs) ⊢ e ∶ (σ <| t)
<|-⊢-∶ σ top = top
<|-⊢-∶ σ {xs} (var x) = var (<|-∋ σ xs x)
<|-⊢-∶ σ (fst ⊢e) = fst (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (snd ⊢e) = snd (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (inl ⊢e) = inl (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (inr ⊢e) = inr (<|-⊢-∶ σ ⊢e)
<|-⊢-∶ σ (⊢e ‵, ⊢f) = (<|-⊢-∶ σ ⊢e) ‵, (<|-⊢-∶ σ ⊢f)

<|-⊢ : (σ : Fin m → Type l) {xs : Vec (Type m) n} {P : Proc n} → xs ⊢ P → (σ <| xs) ⊢ P
<|-⊢ σ end = end
<|-⊢ σ (new t ⊢P) = new _ (<|-⊢ σ ⊢P)
<|-⊢ σ (comp ⊢P ⊢Q) = comp (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)
<|-⊢ σ (recv e ⊢P) = recv (<|-⊢-∶ σ e) (<|-⊢ σ ⊢P)
<|-⊢ σ (send e f ⊢P) = send (<|-⊢-∶ σ e) (<|-⊢-∶ σ f) (<|-⊢ σ ⊢P)
<|-⊢ σ (case e ⊢P ⊢Q) = case (<|-⊢-∶ σ e) (<|-⊢ σ ⊢P) (<|-⊢ σ ⊢Q)


_==_ = unify-sound

{-
inferE : (e : Expr n) → Maybe (Σ[ m ∈ ℕ ] Type m × Ctx n m)
inferE top      = return (! ‵⊤ , fresh)
inferE (var x)  = return (! Vec.lookup fresh x , fresh)
inferE (fst e)  = do ! t , Γ₁ ← inferE e
                     let shape = var zero ‵× var (suc (zero {zero}))
                     ! σ ← unify <[ t ] [ shape ]>
                     return (! [ var zero ]|> σ , σ <|[ Γ₁ ])
inferE (snd e)  = do ! t , Γ₁ ← inferE e
                     let shape = var zero ‵× var (suc (zero {zero}))
                     ! σ ← unify <[ t ] [ shape ]>
                     return (! [ var (suc zero) ]|> σ , σ <|[ Γ₁ ])
inferE (inl e)  = do ! t , Γ₁ ← inferE e
                     return (! <[ t ] ‵+ [ var (zero {zero}) ]> , <[ Γ₁ ])
inferE (inr e)  = do ! t , Γ₁ ← inferE e
                     return (! <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , [ Γ₁ ]>)
inferE (e ‵, f) = do ! t , Γ₁ ← inferE e
                     ! s , Γ₂ ← inferE f
                     ! σ ← unify <[ Γ₁ ] [ Γ₂ ]>
                     return (! (σ <|[ t ]) ‵× ([ s ]|> σ) , σ <|[ Γ₁ ])
-}

inferE : (e : Expr n) → Maybe (Σ[ m ∈ ℕ ] Type m × Ctx n m)
inferE top      = just (_ , ‵⊤ , fresh)
inferE (var x)  = just (_ , Vec.lookup fresh x , fresh)
inferE (fst e)  with inferE e
... | nothing = nothing
... | just (_ , t , Γ₁) with unify <[ t ] [ var zero ‵× var (suc (zero {zero})) ]>
... | nothing = nothing
... | just (_ , σ) = just (_ , [ var zero ]|> σ , σ <|[ Γ₁ ])
inferE (snd e)  with inferE e
... | nothing = nothing
... | just (_ , t , Γ₁) with unify <[ t ] [ var zero ‵× var (suc (zero {zero})) ]>
... | nothing = nothing
... | just (_ , σ) = just (_ , [ var (suc zero) ]|> σ , σ <|[ Γ₁ ])
inferE (inl e)  with inferE e
... | nothing = nothing
... | just (_ , t , Γ₁) = just (_ , <[ t ] ‵+ [ var (zero {zero}) ]> , <[ Γ₁ ])
inferE (inr e)  with inferE e
... | nothing = nothing
... | just (_ , t , Γ₁) = just (_ , <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , [ Γ₁ ]>)
inferE (e ‵, f) with inferE e
... | nothing = nothing
... | just (_ , t , Γ₁) with inferE f
... | nothing = nothing
... | just (_ , s , Γ₂) with unify <[ Γ₁ ] [ Γ₂ ]>
... | nothing = nothing
... | just (_ , σ) = just (_ , (σ <|[ t ]) ‵× ([ s ]|> σ) , σ <|[ Γ₁ ])

{- TODO: inferP from inferP-sound -}
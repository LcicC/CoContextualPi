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

{- Properties of fresh -}

postulate
  fresh-lookup-id : ∀{n m}(Γ : Ctx n m) → Vec.lookup Γ <| fresh ≡ Γ
  fresh-lookup-var : ∀{n}(x : Fin n) → Vec.lookup fresh x ≡ var x

infixr 2 !_
pattern !_ t = _ , t

{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Inference for Expressions %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-}

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


{-
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
-}

{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Inference for Processes %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-}

inferP : (p : Proc n) → Maybe (Σ[ m ∈ ℕ ] Ctx n m)
inferP end          = return (! fresh)
inferP (new p)      = do ! t ∷ Γ ← inferP p
                         return (! Γ)
inferP (comp p q)   = do ! Γ₁ ← inferP p
                         ! Γ₂ ← inferP q
                         ! σ ← unify <[ Γ₁ ] [ Γ₂ ]>
                         return (! σ <|[ Γ₁ ])
inferP (recv e p)   = do ! c , Γ₁ ← inferE e
                         ! v ∷ Γ₂ ← inferP p
                         ! σ ← unify <[ c ∷ Γ₁ ] [ # v ∷ Γ₂ ]>
                         return (! σ <|[ Γ₁ ])
inferP (send e f p) = do ! c , Γ₁ ← inferE e
                         ! v , Γ₂ ← inferE f
                         ! Γ₃ ← inferP p
                         ! σ₁ ← unify <[ c ∷ Γ₁ ] [ # v ∷ Γ₂ ]>
                         ! σ₂ ← unify <[ σ₁ <|[ Γ₁ ] ] [ Γ₃ ]>
                         return (! [ Γ₃ ]|> σ₂)
inferP (case e p q) = do ! v , Γ₁ ← inferE e
                         ! l ∷ Γ₂ ← inferP p
                         ! r ∷ Γ₃ ← inferP q
                         ! σ₁ ← unify <[ Γ₂ ] [ Γ₃ ]>
                         ! σ₂ ← unify <[ v ∷ Γ₁ ] [ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ]>
                         return (! σ₂ <|[ Γ₁ ])
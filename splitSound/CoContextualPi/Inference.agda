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


inferP : (p : Proc n) → Maybe (Σ[ m ∈ ℕ ] Σ[ Γ ∈ Ctx n m ] Γ ⊢ p)
inferP end          = return (! fresh , end)
inferP (new p)      = do ! t ∷ Γ , ⊢p ← inferP p
                         return (! Γ , new t ⊢p)
inferP (comp p q)   = do ! Γ₁ , ⊢p ← inferP p
                         ! Γ₂ , ⊢q ← inferP q
                         ! σ , sound ← <[ Γ₁ ] == [ Γ₂ ]>
                         let ⊢p' = <|-⊢ (sub σ) (<|-⊢ (|> <<) ⊢p)
                         let ⊢q' = <|-⊢ (sub σ) (<|-⊢ (|> >>) ⊢q)
                         return (! σ <|[ Γ₁ ] , comp ⊢p' (subst (_⊢ _) (sym sound) ⊢q'))
                         {-
inferP (recv e p)   = do ! c , Γ₁ , ⊢e ← inferE-sound e
                         ! v ∷ Γ₂ , ⊢p ← inferP p
                         ! σ , sound ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                         let c#v-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                         let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                         let ⊢p' = <|-⊢ (sub σ) (<|-⊢ (|> >>) ⊢p)
                         return (! σ <|[ Γ₁ ] , recv (subst (_ ⊢ _ ∶_) (c#v-sound) ⊢e')
                                (subst (λ ● → (_ ∷ ●) ⊢ _) (sym Γ₁Γ₂-sound) ⊢p'))
inferP (send e f p) = do ! c , Γ₁ , ⊢e ← inferE-sound e
                         ! v , Γ₂ , ⊢f ← inferE-sound f
                         ! Γ₃ , ⊢p ← inferP p
                         ! σ₁ , sound ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                         ! σ₂ , Γ₁Γ₃-sound ← <[ σ₁ <|[ Γ₁ ] ] == [ Γ₃ ]>
                         let c#v-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                         let ⊢e' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> <<) ⊢e)))
                         let ⊢f' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> >>) ⊢f)))
                         let ⊢p' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) ⊢p)
                         return (! [ Γ₃ ]|> σ₂ , send (subst₂ (_⊢ _ ∶_) Γ₁Γ₃-sound (cong (sub σ₂ <|_ ∘ |> << <|_) c#v-sound) ⊢e')
                                  (subst (_⊢ _ ∶ _) (trans (cong (sub σ₂ <|_ ∘ |> << <|_) (sym Γ₁Γ₂-sound)) Γ₁Γ₃-sound) ⊢f')
                                           ⊢p')
inferP (case e p q) = do ! v , Γ₁ , ⊢e ← inferE-sound e
                         ! l ∷ Γ₂ , ⊢p ← inferP p
                         ! r ∷ Γ₃ , ⊢q ← inferP q
                         ! σ₁ , Γ₂Γ₃-sound ← <[ Γ₂ ] == [ Γ₃ ]>
                         ! σ₂ , sound ← <[ v ∷ Γ₁ ] == [ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ]>
                         let lrv-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                         let ⊢e' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) ⊢e)
                         let ⊢p' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (<|-⊢ (sub σ₁) (<|-⊢ (|> <<) ⊢p)))
                         let ⊢q' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (<|-⊢ (sub σ₁) (<|-⊢ (|> >>) ⊢q)))
                         return (! σ₂ <|[ Γ₁ ] , case (subst (_ ⊢ _ ∶_) lrv-sound ⊢e')
                                  (subst (λ ● → (_ ∷ ●) ⊢ _) (sym Γ₁Γ₂-sound) ⊢p')
                                    (subst (λ ● → (_ ∷ ●) ⊢ _) (sym (trans Γ₁Γ₂-sound (cong (sub σ₂ <|_ ∘ |> >> <|_) Γ₂Γ₃-sound))) ⊢q'))
-}
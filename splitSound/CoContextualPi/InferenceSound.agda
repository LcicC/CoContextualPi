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

module CoContextualPi.InferenceSound where

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

inferE-sound : (e : Expr n) → Maybe (Σ[ m ∈ ℕ ] Σ[ t ∈ Type m ] Σ[ Γ ∈ Ctx n m ] Γ ⊢ e ∶ t)
inferE-sound top      = return (! ‵⊤ , fresh , top)
inferE-sound (var x)  = return (! Vec.lookup fresh x , fresh , var refl)
inferE-sound (fst e)  = do ! t , Γ₁ , ⊢e ← inferE-sound e
                           let shape = var zero ‵× var (suc (zero {zero}))
                           ! σ , sound ← <[ t ] == [ shape ]>
                           let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                           return (! [ var zero ]|> σ , σ <|[ Γ₁ ] , fst (subst (_ ⊢ _ ∶_) sound ⊢e'))
inferE-sound (snd e)  = do ! t , Γ₁ , ⊢e ← inferE-sound e
                           let shape = var zero ‵× var (suc (zero {zero}))
                           ! σ , sound ← <[ t ] == [ shape ]>
                           let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                           return (! [ var (suc zero) ]|> σ , σ <|[ Γ₁ ] , snd (subst (_ ⊢ _ ∶_) sound ⊢e'))
inferE-sound (inl e)  = do ! t , Γ₁ , ⊢e ← inferE-sound e
                           let ⊢e' = <|-⊢-∶ (|> <<) ⊢e
                           return (! <[ t ] ‵+ [ var (zero {zero}) ]> , <[ Γ₁ ] , inl ⊢e')
inferE-sound (inr e)  = do ! t , Γ₁ , ⊢e ← inferE-sound e
                           let ⊢e' = <|-⊢-∶ (|> >>) ⊢e
                           return (! <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , [ Γ₁ ]> , inr ⊢e')
inferE-sound (e ‵, f) = do ! t , Γ₁ , ⊢e ← inferE-sound e
                           ! s , Γ₂ , ⊢f ← inferE-sound f
                           ! σ , sound ← <[ Γ₁ ] == [ Γ₂ ]>
                           let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                           let ⊢f' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> >>) ⊢f)
                           return (! (σ <|[ t ]) ‵× ([ s ]|> σ) , σ <|[ Γ₁ ] , (⊢e' ‵, subst (_⊢ _ ∶ _) (sym sound) ⊢f'))



inferP-sound : (p : Proc n) → Maybe (Σ[ m ∈ ℕ ] Σ[ Γ ∈ Ctx n m ] Γ ⊢ p)
inferP-sound end          = return (! fresh , end)
inferP-sound (new p)      = do ! t ∷ Γ , ⊢p ← inferP-sound p
                               return (! Γ , new t ⊢p)
inferP-sound (comp p q)   = do ! Γ₁ , ⊢p ← inferP-sound p
                               ! Γ₂ , ⊢q ← inferP-sound q
                               ! σ , sound ← <[ Γ₁ ] == [ Γ₂ ]>
                               let ⊢p' = <|-⊢ (sub σ) (<|-⊢ (|> <<) ⊢p)
                               let ⊢q' = <|-⊢ (sub σ) (<|-⊢ (|> >>) ⊢q)
                               return (! σ <|[ Γ₁ ] , comp ⊢p' (subst (_⊢ _) (sym sound) ⊢q'))
inferP-sound (recv e p)   = do ! c , Γ₁ , ⊢e ← inferE-sound e
                               ! v ∷ Γ₂ , ⊢p ← inferP-sound p
                               ! σ , sound ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                               let c#v-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                               let ⊢e' = <|-⊢-∶ (sub σ) (<|-⊢-∶ (|> <<) ⊢e)
                               let ⊢p' = <|-⊢ (sub σ) (<|-⊢ (|> >>) ⊢p)
                               return (! σ <|[ Γ₁ ] , recv (subst (_ ⊢ _ ∶_) (c#v-sound) ⊢e')
                                                    (subst (λ ● → (_ ∷ ●) ⊢ _) (sym Γ₁Γ₂-sound) ⊢p'))
inferP-sound (send e f p) = do ! c , Γ₁ , ⊢e ← inferE-sound e
                               ! v , Γ₂ , ⊢f ← inferE-sound f
                               ! Γ₃ , ⊢p ← inferP-sound p
                               ! σ₁ , sound ← <[ c ∷ Γ₁ ] == [ # v ∷ Γ₂ ]>
                               ! σ₂ , Γ₁Γ₃-sound ← <[ σ₁ <|[ Γ₁ ] ] == [ Γ₃ ]>
                               let c#v-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                               let ⊢e' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> <<) ⊢e)))
                               let ⊢f' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) (<|-⊢-∶ (sub σ₁) (<|-⊢-∶ (|> >>) ⊢f)))
                               let ⊢p' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) ⊢p)
                               return (! [ Γ₃ ]|> σ₂ , send (subst₂ (_⊢ _ ∶_) Γ₁Γ₃-sound (cong (sub σ₂ <|_ ∘ |> << <|_) c#v-sound) ⊢e')
                                                     (subst (_⊢ _ ∶ _) (trans (cong (sub σ₂ <|_ ∘ |> << <|_) (sym Γ₁Γ₂-sound)) Γ₁Γ₃-sound) ⊢f')
                                                     ⊢p')
inferP-sound (case e p q) = do ! v , Γ₁ , ⊢e ← inferE-sound e
                               ! l ∷ Γ₂ , ⊢p ← inferP-sound p
                               ! r ∷ Γ₃ , ⊢q ← inferP-sound q
                               ! σ₁ , Γ₂Γ₃-sound ← <[ Γ₂ ] == [ Γ₃ ]>
                               ! σ₂ , sound ← <[ v ∷ Γ₁ ] == [ (σ₁ <|[ l ]) ‵+ ([ r ]|> σ₁) ∷ σ₁ <|[ Γ₂ ] ]>
                               let lrv-sound , Γ₁Γ₂-sound = Vecₚ.∷-injective sound
                               let ⊢e' = <|-⊢-∶ (sub σ₂) (<|-⊢-∶ (|> <<) ⊢e)
                               let ⊢p' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (<|-⊢ (sub σ₁) (<|-⊢ (|> <<) ⊢p)))
                               let ⊢q' = <|-⊢ (sub σ₂) (<|-⊢ (|> >>) (<|-⊢ (sub σ₁) (<|-⊢ (|> >>) ⊢q)))
                               return (! σ₂ <|[ Γ₁ ] , case (subst (_ ⊢ _ ∶_) lrv-sound ⊢e')
                                                     (subst (λ ● → (_ ∷ ●) ⊢ _) (sym Γ₁Γ₂-sound) ⊢p')
                                                     (subst (λ ● → (_ ∷ ●) ⊢ _) (sym (trans Γ₁Γ₂-sound (cong (sub σ₂ <|_ ∘ |> >> <|_) Γ₂Γ₃-sound))) ⊢q'))

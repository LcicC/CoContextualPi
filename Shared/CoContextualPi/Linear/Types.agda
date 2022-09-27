open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)


module CoContextualPi.Linear.Types where

private
  variable
    n m l k : ℕ


data Cons : ℕ → Set where
  Top  : Cons 0
  ChanI ChanO : Cons 1
  Prod : Cons 2
  Sum  : Cons 2

Cons-dec : (x y : Cons k) → Dec (x ≡ y)
Cons-dec Top Top = yes refl
Cons-dec ChanI ChanI = yes refl
Cons-dec ChanI ChanO = no (λ ())
Cons-dec ChanO ChanI = no (λ ())
Cons-dec ChanO ChanO = yes refl
Cons-dec Prod Prod = yes refl
Cons-dec Prod Sum = no λ ()
Cons-dec Sum Prod = no λ ()
Cons-dec Sum Sum = yes refl

open import CoContextualPi.Unification Cons Cons-dec as Unification
  renaming (Term to Type; UTerm to UType) public
open import CoContextualPi.Unification.Soundness Cons Cons-dec
  using (unify-sound) public
open import CoContextualPi.Unification.Completeness Cons Cons-dec
  using (unify-complete) public
open import CoContextualPi.Unification.Properties Cons Cons-dec public


infixr 25 #o_
infixr 25 #i_
pattern ‵⊤ = Unification.con Top []
pattern #i_ t = Unification.con ChanI (t ∷ [])
pattern #o_ t = Unification.con ChanO (t ∷ [])
pattern _‵×_ t s = Unification.con Prod (t ∷ s ∷ [])
pattern _‵+_ t s = Unification.con Sum (t ∷ s ∷ [])

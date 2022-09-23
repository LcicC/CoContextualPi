open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Bool

open import CoContextualPi.Types

module CoContextualPi.LinearTypeSystem where

private
  variable
    n m l k : ℕ

data Expr : ℕ → Set where
  top  : Expr n
  var  : Fin n  → Expr n
  fst  : Expr n → Expr n
  snd  : Expr n → Expr n
  inl  : Expr n → Expr n
  inr  : Expr n → Expr n
  _‵,_ : Expr n → Expr n → Expr n

data Proc : ℕ → Set where
  end  : Proc n
  new  : Proc (suc n) → Proc n
  comp : Proc n → Proc n → Proc n
  recv : Expr n → Proc (suc n) → Proc n
  send : Expr n → Expr n → Proc n → Proc n
  case : Expr n → Proc (suc n) → Proc (suc n) → Proc n

Ctx : ℕ → ℕ → Set
Ctx n m = Vec (Type m) n

UseCtx : ℕ → Set
UseCtx n = Vec Bool n

allUsed : UseCtx n
allUsed = Vec.replicate true

allNotUsed : UseCtx n
allNotUsed = Vec.replicate false

use : Fin (suc n) → UseCtx (suc n)
use x = Vec.insert allNotUsed x true

private
  variable
    Γ : Ctx n l
    γ γ₁ γ₂ δ₁ δ₂  : UseCtx n
    P Q : Proc n
    e f : Expr n
    t s : Type l
    x y : Fin n


data _≐_•_ : UseCtx n → UseCtx n → UseCtx n → Set where
  empty : [] ≐ [] • []
  left  : γ ≐ γ₁ • γ₂ → (true ∷ γ) ≐ (true ∷ γ₁) • (false ∷ γ₂)
  right : γ ≐ γ₁ • γ₂ → (true ∷ γ) ≐ (false ∷ γ₁) • (true ∷ γ₂)
  nouse : γ ≐ γ₁ • γ₂ → (false ∷ γ) ≐ (false ∷ γ₁) • (false ∷ γ₂)

_∋_∶_ : Ctx n m → Fin n → Type m → Set
Γ ∋ x ∶ t = Vec.lookup Γ x ≡ t

data _؛_⊢_∶_ : Ctx n m → UseCtx n → Expr n → Type m → Set where
  top : Γ ؛ allNotUsed ⊢ top ∶ ‵⊤

  var : Γ ∋ x ∶ t
      → Γ ؛ (use x) ⊢ var x ∶ t

  fst : Γ ؛ γ ⊢ e ∶ (t ‵× s)
      → Γ ؛ γ ⊢ fst e ∶ t

  snd : Γ ؛ γ ⊢ e ∶ (t ‵× s)
      → Γ ؛ γ ⊢ snd e ∶ s

  inl : Γ ؛ γ ⊢ e ∶ t
      → Γ ؛ γ ⊢ inl e ∶ (t ‵+ s)

  inr : Γ ؛ γ ⊢ e ∶ s
      → Γ ؛ γ ⊢ inr e ∶ (t ‵+ s)

  _‵,_ :  Γ ؛ γ ⊢ e ∶ s
        → Γ ؛ γ ⊢ f ∶ t
        → Γ ؛ γ ⊢ (e ‵, f) ∶ (s ‵× t)

data _؛_⊢_ : Ctx n m → UseCtx n → Proc n → Set where
  end : Γ ؛ allNotUsed ⊢ end

  new : (t : Type m)
      → (t ∷ Γ) ؛ (true ∷ γ) ⊢ P
      → Γ ؛ γ ⊢ new P

  comp : γ ≐ γ₁ • γ₂
       → Γ ؛ γ₁ ⊢ P
       → Γ ؛ γ₂ ⊢ Q
       → Γ ؛ γ ⊢ (comp P Q)

  recv : γ ≐ γ₁ • γ₂
       → Γ ؛ γ₁ ⊢ e ∶ # t
       → (t ∷ Γ) ؛ (true ∷ γ₂) ⊢ P
       → Γ ؛ γ ⊢ recv e P

  send : γ ≐ γ₁ • γ₂ → γ₁ ≐ δ₁ • δ₂
       → Γ ؛ δ₁ ⊢ e ∶ # t
       → Γ ؛ δ₂ ⊢ f ∶ t
       → Γ ؛ γ₂ ⊢ P
       → Γ ؛ γ ⊢ send e f P

  case : γ ≐ γ₁ • γ₂
       → Γ ؛ γ₁ ⊢ e ∶ (t ‵+ s)
       → (t ∷ Γ) ؛ (true ∷ γ₂) ⊢ P
       → (s ∷ Γ) ؛ (true ∷ γ₂) ⊢ Q
       → Γ ؛ γ ⊢ (case e P Q)

_⊢_ : Ctx n m → Proc n → Set
Γ ⊢ P = Γ ؛ allUsed ⊢ P

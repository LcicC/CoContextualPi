open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)

open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive as PW using (Pointwise; []; _∷_)
open import Data.Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Category.Functor
open import Category.Monad
open import Category.Applicative
import Data.Maybe.Categorical as maybeCat

open import CoContextualPi.Linear.Types
open import CoContextualPi.Linear.Multiplicities

module CoContextualPi.Linear.TypeSystem where

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
  new  : Proc (suc (suc n)) → Proc n
  comp : Proc n → Proc n → Proc n
  recv : Expr n → Proc (suc n) → Proc n
  send : Expr n → Expr n → Proc n → Proc n
  case : Expr n → Proc (suc n) → Proc (suc n) → Proc n

Ctx : ℕ → ℕ → Set
Ctx n m = Vec (Type m) n

UseCtx : ℕ → Set
UseCtx n = Vec Bool n

infixr 2 !_
pattern !_ t = _ , t

private
  variable
    Γ : Ctx n l
    γ γ₁ γ₂ δ₁ δ₂  : UseCtx n
    P Q : Proc n
    e f : Expr n
    t s : Type l
    x y : Fin n

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
fresh-lookup-var {suc n} zero = refl
fresh-lookup-var {suc n} (suc x) with fresh-lookup-var x
fresh-lookup-var {suc .(suc _)} (suc zero) | eq = refl
fresh-lookup-var {suc .(suc _)} (suc (suc x)) | eq = {!   !}

data _≐_•_ : UseCtx n → UseCtx n → UseCtx n → Set where
  empty : [] ≐ [] • []
  left  : γ ≐ γ₁ • γ₂ → (true ∷ γ) ≐ (true ∷ γ₁) • (false ∷ γ₂)
  right : γ ≐ γ₁ • γ₂ → (true ∷ γ) ≐ (false ∷ γ₁) • (true ∷ γ₂)
  none : γ ≐ γ₁ • γ₂ → (false ∷ γ) ≐ (false ∷ γ₁) • (false ∷ γ₂)

data Un : UseCtx n → Set where
  []ᵘ  : Un []
  _∷ᵘ_ : Un γ → Un (false ∷ γ)

use : Type m → Bool
use (var x) = false
use (#i t) = true
use (#o t) = true
use (t ‵+ s) = false
use (t ‵× s) = false
use ‵⊤ = false

data _؛_∋_∶_ : Ctx n m → UseCtx n → Fin n → Type m → Set where
  zvar : Un γ →  (t ∷ Γ) ؛ (use t ∷ γ) ∋ zero ∶ t
  svar : Γ ؛ γ ∋ x ∶ t → (s ∷ Γ) ؛ (false ∷ γ) ∋ (suc x) ∶ t

data _؛_⊢_∶_ : Ctx n m → UseCtx n → Expr n → Type m → Set where
  top : Un γ → Γ ؛ γ ⊢ top ∶ ‵⊤

  var : Γ ؛ γ ∋ x ∶ t
      → Γ ؛ γ ⊢ var x ∶ t

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
  end : Un γ →  Γ ؛ γ ⊢ end

  new : (t : Type m)
      → ((#o t) ∷ (#i t) ∷ Γ) ؛ (true ∷ true ∷ γ) ⊢ P
      → Γ ؛ γ ⊢ new P

  comp : γ ≐ γ₁ • γ₂
       → Γ ؛ γ₁ ⊢ P
       → Γ ؛ γ₂ ⊢ Q
       → Γ ؛ γ ⊢ (comp P Q)

  recv : γ ≐ γ₁ • γ₂
       → Γ ؛ γ₁ ⊢ e ∶ #i t
       → (t ∷ Γ) ؛ ((use t) ∷ γ₂) ⊢ P
       → Γ ؛ γ ⊢ recv e P

  send : γ ≐ γ₁ • γ₂ → γ₁ ≐ δ₁ • δ₂
       → Γ ؛ δ₁ ⊢ e ∶ #o t
       → Γ ؛ δ₂ ⊢ f ∶ t
       → Γ ؛ γ₂ ⊢ P
       → Γ ؛ γ ⊢ send e f P

  case : γ ≐ γ₁ • γ₂
       → Γ ؛ γ₁ ⊢ e ∶ (t ‵+ s)
       → (t ∷ Γ) ؛ ((use t) ∷ γ₂) ⊢ P
       → (s ∷ Γ) ؛ ((use s) ∷ γ₂) ⊢ Q
       → Γ ؛ γ ⊢ (case e P Q)

allUsed : Ctx n m → UseCtx n
allUsed Γ = Vec.map use Γ

_⊢_ : Ctx n m → Proc n → Set
Γ ⊢ P = Γ ؛ allUsed Γ ⊢ P

{-
-- Il vettore di usi deve essere <= di quello di tipo
inferE : (e : Expr n) → Maybe (Σ[ m ∈ ℕ ] Type m × Ctx n m × ExtUseCtx n)
inferE top      = return (! ‵⊤ , fresh , VecOf ω)
inferE (var x)  = return (! Vec.lookup fresh x , fresh , (place once at x else unused))
inferE (fst e)  = do ! t , Γ₁ , Δ₁ ← inferE e
                     let shape = var zero ‵× var (suc (zero {zero}))
                     ! σ ← unify <[ t ] [ shape ]>
                     return (! [ var zero ]|> σ , σ <|[ Γ₁ ] , Δ₁)
inferE (snd e)  = do ! t , Γ₁ , Δ₂ ← inferE e
                     let shape = var zero ‵× var (suc (zero {zero}))
                     ! σ ← unify <[ t ] [ shape ]>
                     return (! [ var (suc zero) ]|> σ , σ <|[ Γ₁ ] , Δ₂)
inferE (inl e)  = do ! t , Γ₁ , Δ₁ ← inferE e
                     return (! <[ t ] ‵+ [ var (zero {zero}) ]> , <[ Γ₁ ] , Δ₁)
inferE (inr e)  = do ! t , Γ₁ , Δ₂ ← inferE e
                     return (! <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , [ Γ₁ ]> , Δ₂)
inferE (e ‵, f) = do ! t , Γ₁ , Δ₁ ← inferE e
                     ! s , Γ₂ , Δ₂ ← inferE f
                     ! σ ← unify <[ Γ₁ ] [ Γ₂ ]>
                     -- return pointwise sum of usages
                     return (! (σ <|[ t ]) ‵× ([ s ]|> σ) , σ <|[ Γ₁ ] , Vec.zipWith _+ₘ_ Δ₁ Δ₂)
              -}

ω≤fresh : VecOf {n} ω ≤ₘₗ Vec.map upper-bound fresh
ω≤fresh {n = zero} = []
ω≤fresh {n = suc n} = 
  let rec = ω≤fresh {n = n} in
  reflex ∷ {!   !}

inferE : (e : Expr n) → Maybe (Σ[ m ∈ ℕ ] Type m × (Σ[ (Γ , Δ) ∈ Ctx n m × ExtUseCtx n ]  Δ ≤ₘₗ Vec.map upper-bound Γ))
inferE top      = return (! ‵⊤ , ((fresh , VecOf ω) , ω≤fresh))
inferE (var x)  = return (! Vec.lookup fresh x , ((fresh , (place once at x else unused)) , {!   !}))
inferE (fst e)  = do ! t , ((Γ₁ , Δ₁) , _) ← inferE e
                     let shape = var zero ‵× var (suc (zero {zero}))
                     ! σ ← unify <[ t ] [ shape ]>
                     return (! [ var zero ]|> σ , ((σ <|[ Γ₁ ] , Δ₁) , {!   !}))
inferE (snd e)  = do ! t , ((Γ₁ , Δ₂) , _) ← inferE e
                     let shape = var zero ‵× var (suc (zero {zero}))
                     ! σ ← unify <[ t ] [ shape ]>
                     return (! [ var (suc zero) ]|> σ , ((σ <|[ Γ₁ ] , Δ₂) , {!   !}))
inferE (inl e)  = do ! t , ((Γ₁ , Δ₁) , _) ← inferE e
                     return (! <[ t ] ‵+ [ var (zero {zero}) ]> , ((<[ Γ₁ ] , Δ₁) , {!   !}))
inferE (inr e)  = do ! t , ((Γ₁ , Δ₂) , _) ← inferE e
                     return (! <[ var (zero {zero}) ] ‵+ [_]> {m = 1} t , (([ Γ₁ ]> , Δ₂) , {!   !}))
inferE (e ‵, f) = do ! t , ((Γ₁ , Δ₁) , _) ← inferE e
                     ! s , ((Γ₂ , Δ₂) , _) ← inferE f
                     ! σ ← unify <[ Γ₁ ] [ Γ₂ ]>
                     -- return pointwise sum of usages
                     return (! (σ <|[ t ]) ‵× ([ s ]|> σ) , ((σ <|[ Γ₁ ] , Vec.zipWith _+ₘ_ Δ₁ Δ₂) , {!   !}))
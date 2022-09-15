open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst; subst₂; cong-app; cong₂)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Function using (id)
open import Function.Reasoning using () renaming (_|>_ to _|>>_)
open import Category.Functor
open import Category.Monad
open import Category.Applicative
open import Function using (_∘_)

open import Data.Unit as Unit using (⊤; tt)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.List as List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)

import Data.Maybe.Categorical as maybeCat
import Data.Nat.Properties as ℕₚ
import Data.Fin.Properties as Finₚ
import Data.Vec.Properties as Vecₚ
import Data.List.Properties as Listₚ
import Data.List.Relation.Unary.All.Properties as Allₚ

open import CoContextualPi.Types
open Unification using (|>; _<|_; var; con; zero; suc; !_)
open import CoContextualPi.TypeSystem
open import CoContextualPi.Constr

module CoContextualPi.Inference where

private
  variable
    u : Univ
    n m l : ℕ
    k k₁ k₂ k₃ : Kind
    γ δ θ ξ : KindCtx
    x y z i o iₗ iᵣ oₗ oᵣ : Usage γ
    t s r sₗ sᵣ tₗ tᵣ : Type γ
    Γ Δ Θ : Ctx n γ

private
  -- Help ourselves to some goodies
  open RawFunctor {{...}}
  open RawApplicative {{...}} hiding (_<$>_)
  open RawMonad {{...}} hiding (_<$>_; _⊛_)
  instance maybeFunctor = maybeCat.functor
  instance maybeMonad = maybeCat.monad
  instance maybeApplicative = maybeCat.applicative

{-
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%% Inference for Expressions %%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-}

inferE : ∀ {δ} (e : Expr n) → Σ[ γ ∈ KindCtx ] Ctx n γ × Type γ × List (Constr γ)
inferE {n = n} {δ} top =
  let γ , Γ = fresh in
  let cs , _ = un-constr {n = n} {γ} {δ} Γ in
   _ , Γ , ‵⊤ , cs
inferE {n = suc n} {δ} (var i) =
  let γ , Γ = fresh in
  let cs , _ = un-var {n = suc n} {γ} {δ} i Γ in
   _ , Γ , Vec.lookup Γ i , cs
inferE {δ = δ} (fst e) =
  let γ , Γ , t , cs = inferE {δ = δ} e in
  let +-un-s , _ = un-constr¹ {δ = δ} (var (! (suc zero))) in
  let +2 = λ {k} → |> {k = k} (!suc ∘ !suc) in
  type ∷ type ∷ γ , +2 <|ᵛ Γ , var (! zero) , 
  [ +2 <| t == var (! zero) ‵× var (! suc zero) ] ∷ +-un-s ∷ (+2 <|ᶜ cs)
inferE {δ = δ} (snd e) =
  let γ , Γ , t , cs = inferE {δ = δ} e in
  let +-un-s , _ = un-constr¹ {δ = δ} (var (! (suc zero))) in
  let +2 = λ {k} → |> {k = k} (!suc ∘ !suc) in
  type ∷ type ∷ γ , +2 <|ᵛ Γ , var (! zero) , 
  [ +2 <| t == var (! (suc zero)) ‵× var (! zero) ] ∷ +-un-s ∷ (+2 <|ᶜ cs)
inferE {δ = δ} (inl e) =
  let γ , Γ , t , cs = inferE {δ = δ} e in
  type ∷ γ , |> !suc <|ᵛ Γ , ((|> !suc <| t) ‵+ var !zero) , (|> !suc <|ᶜ cs)
inferE {δ = δ} (inr e) =
  let γ , Γ , t , cs = inferE {δ = δ} e in
  type ∷ γ , |> !suc <|ᵛ Γ , (var !zero ‵+ (|> !suc <| t)) , (|> !suc <|ᶜ cs)
inferE {δ = δ} (l ‵, r) =
  let lγ , lΓ , lt , lcs = inferE {δ = δ} l in
  let rγ , rΓ , rt , rcs = inferE {δ = δ} r in
  let mγ , mΓ = fresh in
  let congr = map-==-+ mΓ lΓ rΓ in
  let left = (|> (>> {δ = mγ}) ∘ <<) <|ᶜ lcs in
  let right = (|> (>> {δ = mγ}) ∘ >>) <|ᶜ rcs in
  mγ List.++ lγ List.++ rγ , |> << <|ᵛ mΓ , 
  |> (>> {δ = mγ}) <| ((|> << <| lt) ‵× (|> >> <| rt)) , 
  congr List.++ (left List.++ right)

{-
constrProc : (p : Proc n) → Σ[ γ ∈ KindCtx ] Σ[ Γ ∈ Ctx n γ ] ∀⟦ σ ∶ γ ↦ δ ⟧ ((σ <|ᵛ Γ) ⊢ p)
constrProc end =
  let γ , Γ = fresh in
  let cs , f = un-constr Γ in
  _ , Γ , cs , λ σ x → end (f σ x)
constrProc (new p)
  with γ , (t ∷ Γ) , cs , f ← constrProc p
  = γ , Γ , cs , λ σ x → new (σ <| t) (f σ x)
constrProc (comp p p₁) = {!!}
constrProc (recv x p) = {!!}
constrProc (send x x₁ p) = {!!}
constrProc (case x p p₁) = {!!}
-}
module Stlc where

open import Data.Product
open import Data.Sum

open import Relation.Binary.PropositionalEquality

-- Types

data Ty : Set where
  ○ : Ty
  _⇒_ : (σ τ : Ty) → Ty

-- Contexts

data Con : Set where
  ε : Con
  _,_ : (Γ : Con) → (σ : Ty) → Con


-- Variables (De Bruijn indices)

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ , σ) σ
  vs : ∀ {Γ σ τ} → (x : Var Γ σ) → Var (Γ , τ) σ

-- Terms

data Tm : Con → Ty → Set where
  var : ∀ {Γ σ} → (x : Var Γ σ) → Tm Γ σ
  ƛ   : ∀ {Γ σ τ} → (t : Tm (Γ , σ) τ) → Tm Γ (σ ⇒ τ)
  _·_ : ∀ {Γ σ τ} → (t₁ : Tm Γ (σ ⇒ τ)) → (t₂ : Tm Γ σ) → Tm Γ τ

-- Removing a variable from a context

_-_ : {σ : Ty} → (Γ : Con) → (x : Var Γ σ) → Con
ε - ()
(Γ , σ) - vz = Γ
(Γ , τ) - (vs x) = (Γ - x) , τ

-- Weakening

_⇗ˣ_ : ∀ {Γ σ τ} (x : Var Γ σ) → (v : Var (Γ - x) τ) →  Var Γ τ

vz   ⇗ˣ v = vs v
vs x ⇗ˣ vz = vz
vs x ⇗ˣ vs v = vs (x ⇗ˣ v)

-- Variable equality

data VarDiff {Γ : Con} : {σ τ : Ty} → (x : Var Γ σ) (v : Var Γ τ) → Set where
  ⟳ˣ   : ∀ {σ} {x : Var Γ σ} → VarDiff x x
  _↗ˣ_ : ∀ {σ τ} (x : Var Γ σ) (v : Var (Γ - x) τ) → VarDiff x (x ⇗ˣ v)

varDiff : ∀ {Γ σ τ} → (x : Var Γ σ) (v : Var Γ τ) → VarDiff x v

varDiff vz vz = ⟳ˣ
varDiff vz (vs x) = vz ↗ˣ x
varDiff (vs x) vz = vs x ↗ˣ vz
varDiff (vs x) (vs v) with varDiff x v
varDiff (vs x) (vs .x) | ⟳ˣ = ⟳ˣ
varDiff (vs x) (vs .(x ⇗ˣ v)) | .x ↗ˣ v = vs x ↗ˣ vs v

-- Term weakening

_⇗_ : ∀ {Γ σ τ} (x : Var Γ σ) → (v : Tm (Γ - x) τ) →  Tm Γ τ

x ⇗ var v = var (x ⇗ˣ v)
x ⇗ ƛ t = ƛ (vs x ⇗ t)
x ⇗ (t₁ · t₂) = (x ⇗ t₁) · (x ⇗ t₂)

-- Substitution

-- By construction:
-- (1) substitution is type preserving,
-- (2) x does not appear free in the result.

substVar : ∀ {Γ σ τ} (v : Var Γ τ) (x : Var Γ σ) (t : Tm (Γ - x) σ) →
             Tm (Γ - x) τ

substVar v x t with varDiff x v
substVar .x x t | ⟳ˣ = t
substVar .(x ⇗ˣ v) x t | .x ↗ˣ v = var v

substTm : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) (u : Tm (Γ - x) σ) →
             Tm (Γ - x) τ

substTm (var v) x u = substVar v x u
substTm (ƛ t) x u = ƛ (substTm t (vs x) (vz ⇗ u))
substTm (t₁ · t₂) x u = substTm t₁ x u · substTm t₂ x u


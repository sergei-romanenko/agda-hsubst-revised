module BetaEta where

open import Data.Star

open import Stlc
open import Normalization

infix 4 _≈βη¹_ _≈βη_

-- One-step convertibility

data _≈βη¹_ : {Γ : Con} {σ : Ty} (t₁ t₂ : Tm Γ σ) → Set where
  βη-sym : ∀ {Γ σ} {t₁ t₂ : Tm Γ σ} →
            t₁ ≈βη¹ t₂ → t₂ ≈βη¹ t₁
  ƛ-cong : ∀ {Γ σ τ} {t₁ t₂ : Tm (Γ , σ) τ} →
            t₁ ≈βη¹ t₂ → ƛ t₁ ≈βη¹ ƛ t₂
  ·-cong : ∀ {Γ σ τ} {t₁ t₂ : Tm Γ (σ ⇒ τ)} {u₁ u₂ : Tm Γ σ} →
            t₁ ≈βη¹ t₂ → u₁ ≈βη¹ u₂ → t₁ · u₁ ≈βη¹ t₂ · u₂
  ≈-β : ∀ {Γ σ τ} {t : Tm (Γ , σ) τ} {u : Tm Γ σ} →
          ((ƛ t) · u) ≈βη¹ substTm t vz u
  ≈-η : ∀ {Γ σ τ} {t : Tm (Γ , σ) (σ ⇒ τ)} →
          ƛ ((vz ⇗ t) · (var vz)) ≈βη¹ t


-- Multi-step convertibility

_≈βη_ : ∀ {Γ σ} (t₁ t₂ : Tm Γ σ) → Set
_≈βη_ = Star _≈βη¹_


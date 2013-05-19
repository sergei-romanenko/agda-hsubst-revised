module BetaEta where

open import Relation.Binary
  using (Setoid)

import Relation.Binary.EqReasoning as EqR

open import Stlc
open import Normalization


infix 4 _≈βη_

-- Convertibility

data _≈βη_ {Γ : Con} : {σ : Ty} (t₁ t₂ : Tm Γ σ) → Set where
  βη-refl : ∀ {σ} {t : Tm Γ σ} →
              t ≈βη t
  βη-sym  : ∀ {σ} {t₁ t₂ : Tm Γ σ} →
              t₁ ≈βη t₂ → t₂ ≈βη t₁
  βη-trans : ∀ {σ} {t₁ t₂ t₃ : Tm Γ σ} →
               t₁ ≈βη t₂ → t₂ ≈βη t₃ → t₁ ≈βη t₃
  ƛ-cong : ∀ {σ τ} {t₁ t₂ : Tm (Γ , σ) τ} →
             t₁ ≈βη t₂ → ƛ t₁ ≈βη ƛ t₂
  ·-cong : ∀ {σ τ} {t₁ t₂ : Tm Γ (σ ⇒ τ)} {u₁ u₂ : Tm Γ σ} →
             t₁ ≈βη t₂ → u₁ ≈βη u₂ → t₁ · u₁ ≈βη t₂ · u₂
  ≈-β : ∀ {σ τ} {t : Tm (Γ , σ) τ} {u : Tm Γ σ} →
          ((ƛ t) · u) ≈βη substTm t vz u
  ≈-η : ∀ {σ τ} {t : Tm Γ (σ ⇒ τ)} →
          ƛ ((vz ⇗ t) · (var vz)) ≈βη t


βη-setoid : {Γ : Con} {σ : Ty} → Setoid _ _

βη-setoid {Γ} {σ} = record
  { Carrier = Tm Γ σ
  ; _≈_ = _≈βη_
  ; isEquivalence = record
    { refl = βη-refl
    ; sym = βη-sym
    ; trans = βη-trans } }

module βη-Reasoning {Γ : Con} {σ : Ty} = EqR (βη-setoid {Γ} {σ})

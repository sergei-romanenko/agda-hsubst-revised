--
-- Terms are convertible to their normal forms
--     ⌈ nf t ⌉ ≈βη t
--

module Soundness where

open import Function
import Function.Related as Related

open import Relation.Binary.PropositionalEquality as P

open import Stlc
open import Normalization
open import BetaEta

postulate

  nf∘⇗ : ∀ {Γ σ τ} (x : Var Γ σ) (t : Tm (Γ - x) τ) →
    nf (x ⇗ t) ≡ x ⇗ⁿ (nf t)

-- The η-equality is true for normal forms

postulate

   ƛⁿ∘·β : ∀ {Γ σ τ} (n : Nf Γ (σ ⇒ τ))  →
    ƛⁿ ((vz ⇗ⁿ n) ·β (vz ·η ε)) ≡ n

-- Normalization and substitution commute.

postulate

  nf∘[≔] : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) (u : Tm (Γ - x) σ) →
    (nf t) [ x ≔ nf u ] ≡ nf (substTm t x u)

--
-- ≈βη⇒nf≡ - "soundness". If two terms are βη-convertible to each other
-- they have the same normal form.
--
-- (Hence, some authors would here prefer the term "completeness".
-- 

-- ≈βη⇒≡nf

≈βη⇒≡nf : ∀ {Γ σ} {t₁ t₂ : Tm Γ σ} → t₁ ≈βη t₂ → nf t₁ ≡ nf t₂

≈βη⇒≡nf βη-refl =
  refl

≈βη⇒≡nf (βη-sym h) =
  sym (≈βη⇒≡nf h)

≈βη⇒≡nf (βη-trans h₁ h₂) =
  trans (≈βη⇒≡nf h₁) (≈βη⇒≡nf h₂)

≈βη⇒≡nf (ƛ-cong h) =
  cong ƛⁿ (≈βη⇒≡nf h)

≈βη⇒≡nf (·-cong h₁ h₂) =
  cong₂ _·β_ (≈βη⇒≡nf h₁) (≈βη⇒≡nf h₂)

≈βη⇒≡nf (≈-β {σ} {τ} {t} {u}) = begin
  nf (ƛ t · u)
    ≡⟨⟩
  nf t [ vz ≔ nf u ]
    ≡⟨ nf∘[≔] t vz u ⟩
  nf (substTm t vz u)
  ∎
  where open ≡-Reasoning

≈βη⇒≡nf (≈-η {σ} {τ} {t}) = begin
  nf (ƛ ((vz ⇗ t) · var vz))
    ≡⟨⟩
  ƛⁿ (nf (vz ⇗ t) ·β (vz ·η ε))
    ≡⟨ cong (λ n → ƛⁿ (n ·β (vz ·η ε))) (nf∘⇗ vz t) ⟩
  ƛⁿ ((vz ⇗ⁿ nf t) ·β (vz ·η ε))
    ≡⟨ ƛⁿ∘·β (nf t) ⟩
  nf t
  ∎
  where open ≡-Reasoning



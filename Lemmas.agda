module Lemmas where

open import Function

open import Relation.Binary.PropositionalEquality as P

open import Stlc
open import Normalization
open import BetaEta


-- _<,<_
-- `Γ₁≡Γ₂ <,< σ` is a shortcut for `cong (flip _,_ σ) Γ₁≡Γ₂`

_<,<_ : {Γ₁ Γ₂ : Con} (p : Γ₁ ≡ Γ₂) (σ : Ty) →
  _≡_ {A = Con} (Γ₁ , σ) (Γ₂ , σ)
refl <,< σ = refl

-- _/Var/_
-- `Γ₁≡Γ₂ /Var/ t` is a shortcut for `subst (flip Var σ) Γ₁≡Γ₂ t`

_/Var/_ : ∀ {Γ₁ Γ₂ σ} → Γ₁ ≡ Γ₂ → Var Γ₁ σ → Var Γ₂ σ
refl /Var/ t = t

-- _/Tm/_
-- `Γ₁≡Γ₂ /Tm/ t` is a shortcut for `subst (flip Tm σ) Γ₁≡Γ₂ t`

_/Tm/_ : ∀ {Γ₁ Γ₂ σ} → Γ₁ ≡ Γ₂ → Tm Γ₁ σ → Tm Γ₂ σ
refl /Tm/ t = t


-- _⇘ˣ_

_⇘ˣ_ : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ) → Var (Γ - (x ⇗ˣ y)) σ

vz   ⇘ˣ y    = vz
vs x ⇘ˣ vz   = x
vs x ⇘ˣ vs y = vs (x ⇘ˣ y)

-∘- : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ) →
              (Γ - x) - y ≡ (Γ - (x ⇗ˣ y)) - (x ⇘ˣ y)

-∘- vz y = refl
-∘- (vs x) vz = refl
-∘- (vs {τ = τ} x) (vs y) = (-∘- x y) <,< τ


-- /Var/∘var

/Var/∘var : ∀ {Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (z : Var Γ₁ τ) →
  p /Tm/ (var z) ≡ var (p /Var/ z)

/Var/∘var refl z = refl

-- /Tm/∘var

/Tm/∘var : ∀ {σ Γ₁ Γ₂} (p : Γ₁ ≡ Γ₂) (v : Var Γ₁ σ) →
  p /Tm/ (var v) ≡ var (p /Var/ v)

/Tm/∘var refl _ = refl

-- /Tm/∘ƛ

/Tm/∘ƛ : ∀ {σ Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (t : Tm (Γ₁ , σ) τ) →
  p /Tm/ (ƛ t) ≡ ƛ ((p <,< σ) /Tm/ t)

/Tm/∘ƛ refl _ = refl

-- /Tm/∘·

/Tm/∘· : ∀ {σ Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (t₁ : Tm Γ₁ (σ ⇒ τ)) (t₂ : Tm Γ₁ σ) →
  p /Tm/ (t₁ · t₂) ≡ (p /Tm/ t₁) · (p /Tm/ t₂)

/Tm/∘· refl _ _ = refl


-- /Tm/∘⇗

/Tm/∘vz⇗ : ∀ {σ Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (t : Tm Γ₁ τ) →
  (p <,< σ) /Tm/ (vz ⇗ t) ≡ vz ⇗ (p /Tm/ t)

/Tm/∘vz⇗ refl p = refl


-- /Var/∘vz

/Var/∘vz : ∀ {Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) →
  (p <,< τ) /Var/ vz {Γ₁} ≡ vz {Γ₂} 

/Var/∘vz refl = refl

-- /Var/∘vs

/Var/∘vs : ∀ {Γ₁ Γ₂ σ τ} (p : Γ₁ ≡ Γ₂) (v : Var Γ₁ τ) →
  (p <,< σ) /Var/ vs v ≡ vs (p /Var/ v)

/Var/∘vs refl v = refl


-- varDiff-⟳ˣ

varDiff-⟳ˣ :  ∀ {Γ σ} (x : Var Γ σ) →
  varDiff x x ≡ ⟳ˣ

varDiff-⟳ˣ vz = refl
varDiff-⟳ˣ (vs x) rewrite varDiff-⟳ˣ x = refl

-- varDiff-↗ˣ

varDiff-↗ˣ : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ) →
  varDiff x (x ⇗ˣ y) ≡ x ↗ˣ y

varDiff-↗ˣ vz y = refl
varDiff-↗ˣ (vs x) vz = refl
varDiff-↗ˣ (vs x) (vs y) rewrite varDiff-↗ˣ x y = refl


-- substVar∘⟳ˣ

substVar∘⟳ˣ : ∀ {Γ σ} (x : Var Γ σ) (u : Tm (Γ - x) σ) →
  substVar x x u ≡ u

substVar∘⟳ˣ x u rewrite varDiff-⟳ˣ x =
  refl

-- substVar∘⇗ˣ

substVar∘⇗ˣ : ∀ {Γ σ τ} (x : Var Γ σ) (u : Tm (Γ - x) σ) (v : Var (Γ - x) τ) →
  substVar (x ⇗ˣ v) x u ≡ var v

substVar∘⇗ˣ x u v rewrite varDiff-↗ˣ x v =
  refl


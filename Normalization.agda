module Normalization where

open import Stlc

-- Normal forms.

mutual

  data Nf : Con → Ty → Set where
    ƛ   : ∀ {Γ σ τ} (n : Nf (Γ , σ) τ) → Nf Γ (σ ⇒ τ)
    _·_ : ∀ {Γ σ} (x : Var Γ σ) → (ns : Sp Γ σ ○) → Nf Γ ○
 
  data Sp : Con → Ty → Ty → Set where
    ε : ∀ {Γ σ} → Sp Γ σ σ
    _,_ : ∀ {Γ σ τ₁ τ₂} (n : Nf Γ σ) (ns : Sp Γ τ₁ τ₂) → Sp Γ (σ ⇒ τ₁) τ₂

-- The canonical injection of Nf into Tm.

mutual

  ⌈_⌉ : ∀ {Γ σ} (n : Nf Γ σ) → Tm Γ σ

  ⌈ ƛ n ⌉ = ƛ ⌈ n ⌉
  ⌈ x · ns ⌉ = var x ·⌈ ns ⌉

  _·⌈_⌉ : ∀ {Γ σ τ} (t : Tm Γ σ) (ns : Sp Γ σ τ) → Tm Γ τ

  t ·⌈ ε ⌉ = t
  t ·⌈ n , ns ⌉ = (t · ⌈ n ⌉) ·⌈ ns ⌉

-- Weakening of Nf and Sp

mutual

  _⇗ⁿ_ : ∀ {Γ σ τ} (x : Var Γ σ) (n : Nf (Γ - x) τ) → Nf Γ τ

  x ⇗ⁿ ƛ n = ƛ (vs x ⇗ⁿ n)
  x ⇗ⁿ (y · ns) = (x ⇗ˣ y) · (x ⇗ˢ ns)

  _⇗ˢ_ : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ) (n : Sp (Γ - x) τ₁ τ₂) → Sp Γ τ₁ τ₂

  x ⇗ˢ ε = ε
  x ⇗ˢ (n , ns) = (x ⇗ⁿ n) , (x ⇗ˢ ns)

-- Appending an Nf to a Sp

Sp+Nf : ∀ {Γ σ τ₁ τ₂} (ns : Sp Γ σ (τ₁ ⇒ τ₂)) (n : Nf Γ τ₁) → Sp Γ σ τ₂

Sp+Nf ε n = n , ε
Sp+Nf (n′ , ns) n = n′ , Sp+Nf ns n

-- η-expansion
--  t ↦ (λ v → (t v))

_·η_ : ∀ {τ Γ σ} (x : Var Γ σ) (ns : Sp Γ σ τ) → Nf Γ τ

_·η_ {○} x ns = x · ns
_·η_ {τ₁ ⇒ τ₂} x ns =
  ƛ (vs x ·η (Sp+Nf (vz ⇗ˢ ns) (vz ·η ε)))


-- β-reduction

-- _[_≔_]_  substitutes an Nf for a Var in an Nf.
-- _<_≔_>_  substitutes an Nf for a Var in a Sp.
-- _◇_      applies an Nf to a Sp.
-- _·β_     performs β-reduction.

mutual

  _[_≔_] : ∀ {Γ σ τ} (t : Nf Γ τ) (x : Var Γ σ) (u : Nf (Γ - x) σ) →
              Nf (Γ - x) τ

  (ƛ n) [ x ≔ u ] = ƛ (n [ vs x ≔ vz ⇗ⁿ u ])
  (v · ns) [ x ≔ u ] with varDiff x v
  (.x · ns) [ x ≔ u ] | ⟳ˣ = u ◇ (ns < x ≔ u >)
  (.(x ⇗ˣ v) · ns) [ x ≔ u ] | .x ↗ˣ v = v · (ns < x ≔ u >)

  _<_≔_> : ∀ {Γ σ τ₁ τ₂} (ns : Sp Γ τ₁ τ₂) (x : Var Γ σ) (u : Nf (Γ - x) σ) →
              Sp (Γ - x) τ₁ τ₂

  ε < x ≔ u > = ε
  (n , ns) < x ≔ u > = (n [ x ≔ u ]) , (ns < x ≔ u >)

  _◇_ : ∀ {Γ σ τ} (n : Nf Γ σ) (ns : Sp Γ σ τ) → Nf Γ τ

  n ◇ ε = n
  n ◇ (n′ , ns) = (n ·β n′) ◇ ns

  _·β_ : ∀ {Γ σ τ} (n₁ : Nf Γ (σ ⇒ τ)) (n₂ : Nf Γ σ) → Nf Γ τ

  ƛ n₁ ·β n₂ = n₁ [ vz ≔ n₂ ]

-- The normalization function

nf : ∀ {Γ σ} (t : Tm Γ σ) → Nf Γ σ

nf (var x)   = x ·η ε
nf (ƛ t)     = ƛ (nf t)
nf (t₁ · t₂) = nf t₁ ·β nf t₂
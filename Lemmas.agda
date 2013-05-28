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

-- sym∘<,<

sym∘<,< : ∀ {Γ₁ Γ₂ : Con} (p : Γ₁ ≡ Γ₂) (σ : Ty) →
 (P.sym p) <,< σ ≡ P.sym {_} {Con} (p <,< σ)
sym∘<,< refl σ = refl


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

-- /Var/∘sym

/Var/∘sym : ∀ {σ Γ₁ Γ₂} (x : Var Γ₁ σ) (y : Var Γ₂ σ) (p : Γ₁ ≡ Γ₂) →
  x ≡ sym p /Var/ y → y ≡ p /Var/ x

/Var/∘sym .y y refl refl = refl

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

-- _/Nf/_

_/Nf/_ : ∀ {σ Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Nf Γ₁ σ → Nf Γ₂ σ
refl /Nf/ n = n


-- _/Sp/_

_/Sp/_ : ∀ {σ τ Γ₁ Γ₂} → Γ₁ ≡ Γ₂ → Sp Γ₁ σ τ → Sp Γ₂ σ τ
refl /Sp/ ns = ns


-- /Nf/∘ƛⁿ

/Nf/∘ƛⁿ : ∀ {σ τ Γ₁ Γ₂} (p : Γ₁ ≡ Γ₂) (n : Nf (Γ₁ , σ) τ) →
  p /Nf/ ƛⁿ n ≡ ƛⁿ ((p <,< σ) /Nf/ n)
/Nf/∘ƛⁿ refl _ = refl

-- /Nf/∘·ⁿ

/Nf/∘·ⁿ : ∀ {σ Γ₁ Γ₂} (p : Γ₁ ≡ Γ₂) (x : Var Γ₁ σ) (ns : Sp Γ₁ σ ○) →
  p /Nf/ (x ·ⁿ ns) ≡ (p /Var/ x) ·ⁿ (p /Sp/ ns)
/Nf/∘·ⁿ refl _ _ = refl

-- /Sp/∘ε

/Sp/∘ε : ∀ {σ Γ₁ Γ₂} (p : Γ₁ ≡ Γ₂) → p /Sp/ (ε {σ = σ}) ≡ ε
/Sp/∘ε refl = refl

-- /Sp/∘,

/Sp/∘, : ∀ {σ Γ₁ Γ₂ τ₁ τ₂} (p : Γ₁ ≡ Γ₂) (n : Nf Γ₁ σ) (ns : Sp Γ₁ τ₁ τ₂) →
  p /Sp/ (n , ns) ≡ (p /Nf/ n) , (p /Sp/ ns)
/Sp/∘, refl _ _ = refl


-- ⇗ˣ∘⇗ˣ

⇗ˣ∘⇗ˣ : ∀ {Γ σ₁ σ₂ τ} (x : Var Γ σ₁) (y : Var (Γ - x) σ₂)
          (v : Var ((Γ - x) - y) τ) →
        x ⇗ˣ (y ⇗ˣ v) ≡
          (x ⇗ˣ y) ⇗ˣ ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ v))

⇗ˣ∘⇗ˣ vz y v = refl

⇗ˣ∘⇗ˣ (vs x) vz v = refl

⇗ˣ∘⇗ˣ (vs x) (vs y) (vz {σ = σ}) = begin
  vs x ⇗ˣ (vs y ⇗ˣ vz)
    ≡⟨⟩
  vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ vz)
    ≡⟨ cong (λ z → vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ z))
            (sym $ /Var/∘vz (-∘- x y)) ⟩
  vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ ((-∘- x y <,< σ) /Var/ vz))
    ≡⟨⟩
  (vs x ⇗ˣ vs y) ⇗ˣ ((vs x ⇘ˣ vs y) ⇗ˣ (-∘- (vs x) (vs y) /Var/ vz))
  ∎
  where open ≡-Reasoning

⇗ˣ∘⇗ˣ (vs {Γ} {σ₁} x) (vs {σ = σ₂} {τ = τ′} y) (vs {σ = τ} v) = begin
  vs x ⇗ˣ (vs y ⇗ˣ vs v)
    ≡⟨⟩
  vs (x ⇗ˣ (y ⇗ˣ v))
    ≡⟨ cong vs (⇗ˣ∘⇗ˣ x y v) ⟩
  vs ((x ⇗ˣ y) ⇗ˣ ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ v)))
    ≡⟨ refl ⟩
  vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ vs (-∘- x y /Var/ v))
    ≡⟨ cong (λ z → vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ z))
            (sym $ /Var/∘vs (-∘- x y) v) ⟩
  vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ ((-∘- x y <,< τ′) /Var/ vs v))
    ≡⟨⟩
  (vs x ⇗ˣ vs y) ⇗ˣ ((vs x ⇘ˣ vs y) ⇗ˣ (-∘- (vs x) (vs y) /Var/ vs v))
  ∎
  where open ≡-Reasoning

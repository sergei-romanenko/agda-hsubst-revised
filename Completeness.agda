--
-- Terms are convertible to their normal forms
--     ⌈ nf t ⌉ ≈βη t
--

module Completeness where

open import Function

open import Relation.Binary.PropositionalEquality as P

open import Stlc
open import Normalization
open import BetaEta


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
-∘- (vs {τ = τ} x) (vs y) = cong (flip _,_ τ) (-∘- x y)


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
  p /Tm/ (ƛ t) ≡ ƛ (cong (flip _,_ σ) p /Tm/ t)
/Tm/∘ƛ refl _ = refl

-- /Tm/∘·

/Tm/∘· : ∀ {σ Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (t₁ : Tm Γ₁ (σ ⇒ τ)) (t₂ : Tm Γ₁ σ) →
  p /Tm/ (t₁ · t₂) ≡ (p /Tm/ t₁) · (p /Tm/ t₂)
/Tm/∘· refl _ _ = refl


-- /Tm/∘⇗

/Tm/∘vz⇗ : ∀ {σ Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (t : Tm Γ₁ τ) →
  cong (flip _,_ σ) p /Tm/ (vz ⇗ t) ≡ vz ⇗ (p /Tm/ t)
/Tm/∘vz⇗ refl p = refl


-- vz∘/Var/

vz-/Var/ : ∀ {Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) →
  (vz {Γ₂}) ≡ cong (flip _,_ τ) p /Var/ vz {Γ₁}

vz-/Var/ refl = refl

-- vs∘/Var/

vs∘/Var/ : ∀ {Γ₁ Γ₂ σ τ} (p : Γ₁ ≡ Γ₂)  (v : Var Γ₁ τ) →
  vs (p /Var/ v) ≡ cong (flip _,_ σ) p /Var/ vs v

vs∘/Var/ refl v = refl


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
    ≡⟨ cong (λ z → vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ z)) (vz-/Var/ (-∘- x y)) ⟩
  vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ (cong (flip _,_ σ) (-∘- x y) /Var/ vz))
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
    ≡⟨ cong (λ z → vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ z)) (vs∘/Var/ (-∘- x y) v) ⟩
  vs (x ⇗ˣ y) ⇗ˣ (vs (x ⇘ˣ y) ⇗ˣ (cong (flip _,_ τ′) (-∘- x y) /Var/ vs v))
    ≡⟨⟩
  (vs x ⇗ˣ vs y) ⇗ˣ ((vs x ⇘ˣ vs y) ⇗ˣ (-∘- (vs x) (vs y) /Var/ vs v))
  ∎
  where open ≡-Reasoning

-- ⇗∘⇗

⇗∘⇗ : ∀ {Γ σ₁ σ₂ τ} (x : Var Γ σ₁) (y : Var (Γ - x) σ₂)
           (t : Tm ((Γ - x) - y) τ) →
    x ⇗ (y ⇗ t) ≡
      (x ⇗ˣ y) ⇗ ((x ⇘ˣ  y) ⇗ (-∘- x y /Tm/ t))

⇗∘⇗ x y (var {σ = σ} x₁) = begin
  x ⇗ (y ⇗ var x₁)
    ≡⟨ refl ⟩
  var (x ⇗ˣ (y ⇗ˣ x₁))
    ≡⟨ cong var (⇗ˣ∘⇗ˣ x y x₁) ⟩
  var ((x ⇗ˣ y) ⇗ˣ ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ x₁)))
    ≡⟨ refl ⟩
  (x ⇗ˣ y) ⇗ var ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ x₁))
    ≡⟨ refl ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ var (-∘- x y /Var/ x₁))
    ≡⟨ cong (λ t → (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ t))
            (sym $ /Var/∘var (-∘- x y) x₁) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ var x₁))
  ∎
  where open ≡-Reasoning

⇗∘⇗ {Γ} {σ₁} {σ₂} {σ ⇒ .τ} x y (ƛ {τ = τ} t) = begin
  x ⇗ (y ⇗ ƛ t)
    ≡⟨ refl ⟩
  ƛ (vs x ⇗ (vs y ⇗ t))
    ≡⟨ cong ƛ (⇗∘⇗ (vs x) (vs y) t) ⟩
  ƛ (vs (x ⇗ˣ y) ⇗ (vs (x ⇘ˣ y) ⇗ (cong (flip _,_ σ) (-∘- x y) /Tm/ t)))
    ≡⟨ refl ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ ƛ (cong (flip _,_ σ) (-∘- x y) /Tm/ t))
    ≡⟨ cong (λ u → (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ u))
            (sym $ /Tm/∘ƛ (-∘- x y) t) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ ƛ t))
  ∎
  where open ≡-Reasoning

⇗∘⇗ {Γ} {σ₁} {σ₂} {τ} x y (_·_ {σ = σ′} t₁ t₂) = begin
  x ⇗ (y ⇗ (t₁ · t₂))
    ≡⟨ refl ⟩
  (x ⇗ (y ⇗ t₁)) · (x ⇗ (y ⇗ t₂))
    ≡⟨ cong₂ _·_ (⇗∘⇗ x y t₁) (⇗∘⇗ x y t₂) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ ((-∘- x y /Tm/ t₁) · (-∘- x y /Tm/ t₂)))
    ≡⟨ cong (λ t → (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ t))
            (sym $ /Tm/∘· (-∘- x y) t₁ t₂) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ (t₁ · t₂)))
  ∎
  where open ≡-Reasoning


-- ⇗∘substTm

⇗∘substTm : ∀ {Γ σ σ′ τ} (x : Var Γ σ)
              (y : Var (Γ - x) σ′) (u : Tm ((Γ - x) - y) σ′)
              (t : Tm (Γ - x) τ) →
          (x ⇘ˣ y) ⇗ (-∘- x y /Tm/ substTm t y u) ≡
            substTm (x ⇗ t) (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ u))

⇗∘substTm x y u (var x′) with varDiff y x′

⇗∘substTm x y u (var .y) | ⟳ˣ
  rewrite varDiff-⟳ˣ (x ⇗ˣ y) = refl

⇗∘substTm x y u (var .(y ⇗ˣ v)) | .y ↗ˣ v
  rewrite ⇗ˣ∘⇗ˣ x y v
        | varDiff-↗ˣ (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ v)) = begin
  (x ⇘ˣ y) ⇗ (-∘- x y /Tm/ var v)
    ≡⟨ cong (_⇗_ (x ⇘ˣ y)) (/Tm/∘var (-∘- x y) v) ⟩
  (x ⇘ˣ y) ⇗ (var (-∘- x y /Var/ v))
    ≡⟨⟩
  var ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ v))
  ∎
  where open ≡-Reasoning

⇗∘substTm x y u (ƛ {σ = σ}  t) =
  begin
  (x ⇘ˣ y) ⇗ (-∘- x y /Tm/ substTm (ƛ t) y u)
    ≡⟨⟩
  (x ⇘ˣ y) ⇗ (-∘- x y /Tm/ ƛ (substTm t (vs y) (vz ⇗ u)))
    ≡⟨ cong (_⇗_ (x ⇘ˣ y)) (/Tm/∘ƛ (-∘- x y) (substTm t (vs y) (vz ⇗ u))) ⟩
  (x ⇘ˣ y) ⇗ ƛ (cong (flip _,_ σ) (-∘- x y) /Tm/ substTm t (vs y) (vz ⇗ u))
    ≡⟨⟩
  ƛ ((vs x ⇘ˣ vs y) ⇗ ((-∘- (vs x) (vs y)) /Tm/ substTm t (vs y) (vz ⇗ u)))
    ≡⟨ cong ƛ (⇗∘substTm (vs x) (vs y) (vz ⇗ u) t) ⟩
  ƛ (substTm (vs x ⇗ t) (vs (x ⇗ˣ y))
    (vs (x ⇘ˣ y) ⇗ (cong (flip _,_ σ) (-∘- x y) /Tm/ (vz ⇗ u))))
    ≡⟨ cong (λ z → ƛ (substTm (vs x ⇗ t) (vs (x ⇗ˣ y)) (vs (x ⇘ˣ y) ⇗ z)))
            (/Tm/∘vz⇗ (-∘- x y) u) ⟩
  ƛ (substTm (vs x ⇗ t) (vs (x ⇗ˣ y)) (vs (x ⇘ˣ y) ⇗ (vz ⇗ (-∘- x y /Tm/ u))))
    ≡⟨ cong (λ z → ƛ (substTm (vs x ⇗ t) (vs (x ⇗ˣ y)) z))
            (⇗∘⇗ (vs (x ⇘ˣ y)) vz (-∘- x y /Tm/ u)) ⟩
  ƛ (substTm (vs x ⇗ t) (vs (x ⇗ˣ y)) (vz ⇗ ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ u))))
    ≡⟨⟩
  substTm (x ⇗ ƛ t) (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ u))
  ∎
  where open ≡-Reasoning

⇗∘substTm x y u (t₁ · t₂) = begin
  (x ⇘ˣ y) ⇗ (-∘- x y /Tm/ substTm (t₁ · t₂) y u)
    ≡⟨⟩
  (x ⇘ˣ y) ⇗ (-∘- x y /Tm/ (substTm t₁ y u · substTm t₂ y u))
    ≡⟨ cong (λ t → (x ⇘ˣ y) ⇗ t)
            (/Tm/∘· (-∘- x y) (substTm t₁ y u) (substTm t₂ y u)) ⟩
  (x ⇘ˣ y) ⇗ ((-∘- x y /Tm/ substTm t₁ y u) · (-∘- x y /Tm/ substTm t₂ y u))
    ≡⟨⟩
  ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ substTm t₁ y u)) ·
    ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ substTm t₂ y u))
    ≡⟨ cong₂ _·_ (⇗∘substTm x y u t₁) (⇗∘substTm x y u t₂) ⟩
  substTm (x ⇗ t₁) (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ u)) ·
    substTm (x ⇗ t₂) (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ u))
    ≡⟨⟩
  substTm (x ⇗ (t₁ · t₂)) (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ (-∘- x y /Tm/ u))
  ∎
  where open ≡-Reasoning


-- ⇗-cong

⇗-cong : ∀ {Γ σ τ} (x : Var Γ σ) {t₁ t₂ : Tm (Γ - x) τ} →
           t₁ ≈βη t₂ → x ⇗ t₁ ≈βη x ⇗ t₂

⇗-cong x βη-refl =
  βη-refl
⇗-cong x (βη-sym h) =
  βη-sym (⇗-cong x h)
⇗-cong x (βη-trans h₁ h₂) =
  βη-trans (⇗-cong x h₁) (⇗-cong x h₂)
⇗-cong x (ƛ-cong h) =
  ƛ-cong (⇗-cong (vs x) h)
⇗-cong x (·-cong h₁ h₂) =
  ·-cong (⇗-cong x h₁) (⇗-cong x h₂)
⇗-cong x (≈-β {t = t} {u = u}) =
 begin
  x ⇗ (ƛ t · u)
    ≡⟨ refl ⟩
  ƛ (vs x ⇗ t) · (x ⇗ u)
    ≈⟨ ≈-β ⟩
  substTm (vs x ⇗ t) vz (x ⇗ u)
    ≡⟨ sym $ ⇗∘substTm (vs x) vz u t ⟩
  x ⇗ substTm t vz u
  ∎
  where open βη-Reasoning

⇗-cong x (≈-η {t = t}) = begin
  x ⇗ ƛ ((vz ⇗ t) · var vz)
    ≡⟨ refl ⟩
  ƛ ((vs x ⇗ (vz ⇗ t)) · var vz)
    ≡⟨ cong (λ e → ƛ (e · var vz)) (sym $ ⇗∘⇗ vz x t) ⟩
  ƛ ((vz ⇗ (x ⇗ t)) · var vz)
    ≈⟨ ≈-η ⟩
  x ⇗ t
  ∎
  where open βη-Reasoning

-- substTm-cong

substTm-cong : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) {u₁ u₂ : Tm (Γ - x) σ} →
  u₁ ≈βη u₂ → substTm t x u₁ ≈βη substTm t x u₂

substTm-cong (var x′) x h with varDiff x x′
substTm-cong (var .x) x h | ⟳ˣ =
  h
substTm-cong (var .(x ⇗ˣ v)) x h | .x ↗ˣ v =
  βη-refl
substTm-cong (ƛ t) x h =
  ƛ-cong (substTm-cong t (vs x) (⇗-cong vz h))
substTm-cong (t₁ · t₂) x h =
  ·-cong (substTm-cong t₁ x h) (substTm-cong t₂ x h)

-- ·⌈⌉-cong

·⌈⌉-cong : ∀ {Γ σ τ} {t₁ t₂ : Tm Γ σ} (ns : Sp Γ σ τ) →
             t₁ ≈βη t₂ → t₁ ·⌈ ns ⌉ ≈βη t₂ ·⌈ ns ⌉

·⌈⌉-cong ε h =
  βη-sym (βη-sym h)
·⌈⌉-cong (n , ns) h =
  ·⌈⌉-cong ns (·-cong h βη-refl)

-- ·⌈⌉∘Sp+Nf

·⌈⌉∘Sp+Nf : ∀ {Γ σ τ₁ τ₂} (t : Tm Γ σ) (ns : Sp Γ σ (τ₁ ⇒ τ₂)) (n : Nf Γ τ₁) →
  t ·⌈ Sp+Nf ns n ⌉ ≈βη  (t ·⌈ ns ⌉) ·⌈ n , ε ⌉

·⌈⌉∘Sp+Nf t ε n =
  βη-refl
·⌈⌉∘Sp+Nf t (n′ , ns) n =
  ·⌈⌉∘Sp+Nf (t · ⌈ n′ ⌉) ns n

mutual

  -- ⌈⌉∘⇗ⁿ

  ⌈⌉∘⇗ⁿ : ∀ {Γ σ τ} (x : Var Γ σ) (n : Nf (Γ - x) τ) →
    ⌈ x ⇗ⁿ n ⌉ ≈βη x ⇗ ⌈ n ⌉

  ⌈⌉∘⇗ⁿ x (ƛⁿ n) = begin
    ⌈ x ⇗ⁿ ƛⁿ n ⌉
      ≡⟨ refl ⟩
    ƛ ⌈ vs x ⇗ⁿ n ⌉
      ≈⟨ ƛ-cong (⌈⌉∘⇗ⁿ (vs x) n) ⟩
    ƛ (vs x ⇗ ⌈ n ⌉)
      ≡⟨ refl ⟩
    x ⇗ ⌈ ƛⁿ n ⌉
    ∎
    where open βη-Reasoning

  ⌈⌉∘⇗ⁿ x (x′ ·ⁿ ns) = begin
    ⌈ x ⇗ⁿ (x′ ·ⁿ ns) ⌉
      ≡⟨ refl ⟩
    var (x ⇗ˣ x′) ·⌈ x ⇗ˢ ns ⌉
      ≈⟨ ·⌈⌉∘⇗ⁿ x (var x′) ns ⟩
    x ⇗ (var x′ ·⌈ ns ⌉)
      ≡⟨ refl ⟩
    x ⇗ ⌈ x′ ·ⁿ ns ⌉
    ∎
    where open βη-Reasoning

  ·⌈⌉∘⇗ⁿ : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ)
             (t : Tm (Γ - x) τ₁) (ns : Sp (Γ - x) τ₁ τ₂) →
             (x ⇗ t) ·⌈ x ⇗ˢ ns ⌉ ≈βη x ⇗ (t ·⌈ ns ⌉)

  ·⌈⌉∘⇗ⁿ x t ε =
    βη-refl

  ·⌈⌉∘⇗ⁿ x t (n , ns) = begin
    (x ⇗ t) ·⌈ x ⇗ˢ (n , ns) ⌉
      ≡⟨ refl ⟩
    ((x ⇗ t) · ⌈ x ⇗ⁿ n ⌉) ·⌈ x ⇗ˢ ns ⌉
      ≈⟨ ·⌈⌉-cong (x ⇗ˢ ns)
                  (·-cong βη-refl (⌈⌉∘⇗ⁿ x n)) ⟩
    ((x ⇗ t) · (x ⇗ ⌈ n ⌉)) ·⌈ x ⇗ˢ ns ⌉
      ≈⟨ ·⌈⌉∘⇗ⁿ x (t · ⌈ n ⌉) ns ⟩
    x ⇗ ((t · ⌈ n ⌉) ·⌈ ns ⌉)
      ≡⟨ refl ⟩
    x ⇗ (t ·⌈ n , ns ⌉)
    ∎
    where open βη-Reasoning


-- ⌈⌉∘·η

⌈⌉∘·η : ∀ {τ Γ σ} (x : Var Γ σ) (ns : Sp Γ σ τ) →
  ⌈ x ·η ns ⌉ ≈βη var x ·⌈ ns ⌉

⌈⌉∘·η {○} x ns = βη-refl

⌈⌉∘·η {τ₁ ⇒ τ₂} x ns =
  begin
  ⌈ x ·η ns ⌉
    ≡⟨ refl ⟩
  ƛ ⌈ vs x ·η Sp+Nf (vz ⇗ˢ ns) (vz ·η ε) ⌉
    ≈⟨ ƛ-cong (⌈⌉∘·η (vs x) (Sp+Nf (vz ⇗ˢ ns) (vz ·η ε))) ⟩
  ƛ (var (vs x) ·⌈ Sp+Nf (vz ⇗ˢ ns) (vz ·η ε) ⌉)
    ≈⟨ ƛ-cong (·⌈⌉∘Sp+Nf (var (vs x)) (vz ⇗ˢ ns) (vz ·η ε)) ⟩
  ƛ ((var (vs x) ·⌈ vz ⇗ˢ ns ⌉) · ⌈ vz ·η ε ⌉)
    ≈⟨ ƛ-cong (·-cong (·⌈⌉∘⇗ⁿ vz (var x) ns) (⌈⌉∘·η vz ε)) ⟩
  ƛ ((vz ⇗ (var x ·⌈ ns ⌉)) · var vz)
    ≈⟨ ≈-η ⟩
  var x ·⌈ ns ⌉
   ∎
   where open βη-Reasoning

mutual

  -- ⌈⌉∘[≔]

  ⌈⌉∘[≔] : ∀ {Γ σ τ} (n : Nf Γ τ) (x : Var Γ σ) (u : Nf (Γ - x) σ) →
    ⌈ n [ x ≔ u ] ⌉ ≈βη substTm ⌈ n ⌉ x ⌈ u ⌉

  ⌈⌉∘[≔] (ƛⁿ n) x u = begin
    ⌈ ƛⁿ n [ x ≔ u ] ⌉
      ≡⟨ refl ⟩
    ƛ ⌈ n [ vs x ≔ vz ⇗ⁿ u ] ⌉
      ≈⟨ ƛ-cong (⌈⌉∘[≔] n (vs x) (vz ⇗ⁿ u)) ⟩
    ƛ (substTm ⌈ n ⌉ (vs x) ⌈ vz ⇗ⁿ u ⌉)
      ≈⟨ ƛ-cong (substTm-cong ⌈ n ⌉ (vs x) (⌈⌉∘⇗ⁿ vz u)) ⟩
    ƛ (substTm ⌈ n ⌉ (vs x) (vz ⇗ ⌈ u ⌉))
      ≡⟨ refl ⟩
    substTm ⌈ ƛⁿ n ⌉ x ⌈ u ⌉
    ∎
    where open βη-Reasoning

  ⌈⌉∘[≔] (x′ ·ⁿ ns) x u with varDiff x x′

  ⌈⌉∘[≔] (.x ·ⁿ ns) x u | ⟳ˣ = begin
    ⌈ u ◇ (ns < x ≔ u >) ⌉
      ≈⟨ ⌈⌉∘◇ u (ns < x ≔ u >) ⟩
    ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉
      ≡⟨ sym $ cong (flip _·⌈_⌉ (ns < x ≔ u >)) (substVar∘⟳ˣ x ⌈ u ⌉) ⟩
    substVar x x ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉
      ≈⟨ ⌈⌉∘<≔> (var x) ns x u ⟩
    substTm (var x ·⌈ ns ⌉) x ⌈ u ⌉
    ∎
    where open βη-Reasoning

  ⌈⌉∘[≔] (.(x ⇗ˣ v) ·ⁿ ns) x u | .x ↗ˣ v = begin
    var v ·⌈ ns < x ≔ u > ⌉
      ≡⟨ cong (λ z → z ·⌈ ns < x ≔ u > ⌉)
              (sym $ substVar∘⇗ˣ x ⌈ u ⌉ v) ⟩
    substTm (var (x ⇗ˣ v)) x ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉
      ≈⟨ ⌈⌉∘<≔> (x ⇗ var v) ns x u ⟩
    substTm (var (x ⇗ˣ v) ·⌈ ns ⌉) x ⌈ u ⌉
    ∎
    where open βη-Reasoning

  ⌈⌉∘<≔> : ∀ {Γ σ τ₁ τ₂} (t : Tm Γ τ₁) (ns : Sp Γ τ₁ τ₂)
    (x : Var Γ σ) (u : Nf (Γ - x) σ) →
    substTm t x ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉ ≈βη substTm (t ·⌈ ns ⌉) x ⌈ u ⌉

  ⌈⌉∘<≔> t ε x u =
    βη-refl
  ⌈⌉∘<≔> t (n , ns) x u = begin
    substTm t x ⌈ u ⌉ ·⌈ (n , ns) < x ≔ u > ⌉
      ≡⟨ refl ⟩
    (substTm t x ⌈ u ⌉ · ⌈ n [ x ≔ u ] ⌉) ·⌈ ns < x ≔ u > ⌉
      ≈⟨ ·⌈⌉-cong (ns < x ≔ u >) (·-cong βη-refl (⌈⌉∘[≔] n x u))  ⟩
    (substTm t x ⌈ u ⌉ · substTm ⌈ n ⌉ x ⌈ u ⌉ ) ·⌈ ns < x ≔ u > ⌉
      ≡⟨ refl ⟩
    substTm (t · ⌈ n ⌉) x ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉
      ≈⟨ ⌈⌉∘<≔> (t · ⌈ n ⌉) ns x u ⟩ 
    substTm ((t · ⌈ n ⌉) ·⌈ ns ⌉) x ⌈ u ⌉
      ≡⟨ refl ⟩
    substTm (t ·⌈ n , ns ⌉) x ⌈ u ⌉
    ∎
    where open βη-Reasoning

  -- ⌈⌉∘◇

  ⌈⌉∘◇ : ∀ {Γ σ} (n : Nf Γ σ) (ns : Sp Γ σ ○) →
    ⌈ n ◇ ns ⌉ ≈βη ⌈ n ⌉ ·⌈ ns ⌉

  ⌈⌉∘◇ n ε = βη-refl
  ⌈⌉∘◇ n (n′ , ns) = begin
    ⌈ n ◇ (n′ , ns) ⌉
      ≡⟨ refl ⟩
    ⌈ (n ·β n′) ◇ ns ⌉
      ≈⟨ ⌈⌉∘◇ (n ·β n′) ns ⟩
    ⌈ n ·β n′ ⌉ ·⌈ ns ⌉
      ≈⟨ ·⌈⌉-cong ns (⌈⌉∘·β n n′) ⟩
    (⌈ n ⌉ · ⌈ n′ ⌉) ·⌈ ns ⌉
      ≡⟨ refl ⟩
    ⌈ n ⌉ ·⌈ n′ , ns ⌉
    ∎
    where open βη-Reasoning

  -- ⌈⌉∘·β

  ⌈⌉∘·β : ∀ {Γ σ τ} (n₁ : Nf Γ (σ ⇒ τ)) (n₂ : Nf Γ σ) →
    ⌈ n₁ ·β n₂ ⌉ ≈βη ⌈ n₁ ⌉ · ⌈ n₂ ⌉

  ⌈⌉∘·β (ƛⁿ n₁) n₂ = begin
    ⌈ ƛⁿ n₁ ·β n₂ ⌉
      ≡⟨ refl ⟩
    ⌈ n₁ [ vz ≔ n₂ ] ⌉
      ≈⟨ ⌈⌉∘[≔] n₁ vz n₂ ⟩
    substTm ⌈ n₁ ⌉ vz ⌈ n₂ ⌉
      ≈⟨ βη-sym ≈-β ⟩
    ƛ ⌈ n₁ ⌉ · ⌈ n₂ ⌉
      ≡⟨ refl ⟩
    ⌈ ƛⁿ n₁ ⌉ · ⌈ n₂ ⌉
    ∎
    where open βη-Reasoning


--
-- ⌈⌉∘nf - "completeness"
--
-- Normalization preserves the semantics!
-- (Hence, some authors would here prefer the term "soundness".
-- 

⌈⌉∘nf : ∀ {Γ σ} (t : Tm Γ σ) → ⌈ nf t ⌉ ≈βη t

⌈⌉∘nf (var x) = begin
  ⌈ x ·η ε ⌉
    ≈⟨ ⌈⌉∘·η x ε ⟩
  var x ·⌈ ε ⌉
    ≡⟨ refl ⟩
  var x
  ∎
  where open βη-Reasoning

⌈⌉∘nf (ƛ t) = begin
  ⌈ nf (ƛ t) ⌉
    ≡⟨ refl ⟩
  ƛ ⌈ nf t ⌉
    ≈⟨ ƛ-cong (⌈⌉∘nf t) ⟩
  ƛ t
  ∎
  where open βη-Reasoning

⌈⌉∘nf (t₁ · t₂) = begin
  ⌈ nf (t₁ · t₂) ⌉
    ≡⟨ refl ⟩
  ⌈ nf t₁ ·β nf t₂ ⌉
    ≈⟨ ⌈⌉∘·β (nf t₁) (nf t₂) ⟩
  ⌈ nf t₁ ⌉ · ⌈ nf t₂ ⌉
    ≈⟨ ·-cong (⌈⌉∘nf t₁) (⌈⌉∘nf t₂) ⟩
  t₁ · t₂
  ∎
  where open βη-Reasoning

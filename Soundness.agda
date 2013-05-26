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
open import Lemmas

-- cong for Con

postulate
  ⇗ˣ∘·η : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ) →
    (x ⇗ˣ y) ·η ε ≡ x ⇗ⁿ (y ·η ε)

⇗ˣ∘·η′ : ∀ {τ Γ σ} (x : Var Γ σ) (y : Var (Γ - x) τ) →
  (x ⇗ˣ y) ·η ε ≡ x ⇗ⁿ (y ·η ε)

⇗ˣ∘·η′ {○} x y = refl
⇗ˣ∘·η′ {τ₁ ⇒ τ₂} x y = {!!}

⇗ⁿ∘·η : ∀ {τ Γ σ₁ σ₂} (x : Var Γ σ₁)
          (y : Var (Γ - x) σ₂) (ns : Sp (Γ - x) σ₂ τ) →
  x ⇗ⁿ (y ·η ns) ≡ (x ⇗ˣ y) ·η (x ⇗ˢ ns)

⇗ⁿ∘·η {○} x y ns = refl
⇗ⁿ∘·η {τ₁ ⇒ τ₂} x y ns = begin
  x ⇗ⁿ (y ·η ns)
    ≡⟨⟩
  ƛⁿ (vs x ⇗ⁿ (vs y ·η Sp+Nf (vz ⇗ˢ ns) (vz ·η ε)))
    ≡⟨ cong ƛⁿ (⇗ⁿ∘·η (vs x) (vs y) (Sp+Nf (vz ⇗ˢ ns) (vz ·η ε))) ⟩
  ƛⁿ (vs (x ⇗ˣ y) ·η (vs x ⇗ˢ Sp+Nf (vz ⇗ˢ ns) (vz ·η ε)))
    ≡⟨ {!!} ⟩
  ƛⁿ (vs (x ⇗ˣ y) ·η Sp+Nf (vz ⇗ˢ (x ⇗ˢ ns)) (vz ·η ε))
    ≡⟨⟩
  (x ⇗ˣ y) ·η (x ⇗ˢ ns)
  ∎
  where open ≡-Reasoning

-- cong ƛⁿ {!⇗ⁿ∘·η!}

{-
postulate

  ⇗ⁿ∘[≔] : ∀ {Γ σ σ′ τ} (x : Var Γ σ)
             (n : Nf (Γ - x) τ) (u : Nf (Γ - x) σ′) →
    x ⇗ⁿ (n [ vz ≔ u ]) ≡ (vs x ⇗ⁿ n) [ vz ≔ x ⇗ⁿ u ]
-}

postulate

  ⇗ⁿ∘·β : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ)
            (n₁ : Nf (Γ - x) (τ₁ ⇒ τ₂)) (n₂ : Nf (Γ - x) τ₁) →
    x ⇗ⁿ (n₁ ·β n₂) ≡ (x ⇗ⁿ n₁) ·β (x ⇗ⁿ n₂)

--⇗ⁿ∘·β x (ƛⁿ n₁) n₂ = {!!}

{-
postulate

  nf∘⇗ : ∀ {Γ σ τ} (x : Var Γ σ) (t : Tm (Γ - x) τ) →
    nf (x ⇗ t) ≡ x ⇗ⁿ (nf t)
-}

nf∘⇗ : ∀ {Γ σ τ} (x : Var Γ σ) (t : Tm (Γ - x) τ) →
  nf (x ⇗ t) ≡ x ⇗ⁿ (nf t)

nf∘⇗ x (var x′) =
  ⇗ˣ∘·η x x′
nf∘⇗ x (ƛ t) =
  cong ƛⁿ (nf∘⇗ (vs x) t)
nf∘⇗ x (t₁ · t₂) = begin
  nf (x ⇗ (t₁ · t₂))
    ≡⟨⟩
  nf (x ⇗ t₁) ·β nf (x ⇗ t₂)
    ≡⟨ cong₂ _·β_ (nf∘⇗ x t₁) (nf∘⇗ x t₂) ⟩
  (x ⇗ⁿ nf t₁) ·β (x ⇗ⁿ nf t₂)
    ≡⟨ sym $ ⇗ⁿ∘·β x (nf t₁) (nf t₂) ⟩
  x ⇗ⁿ (nf t₁ ·β nf t₂)
    ≡⟨⟩
  x ⇗ⁿ nf (t₁ · t₂)
  ∎
  where open ≡-Reasoning

-- Normalization and substitution commute.

postulate

  nf∘[≔] : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) (u : Tm (Γ - x) σ) →
    (nf t) [ x ≔ nf u ] ≡ nf (substTm t x u)

-- The η-equality is true for normal forms


-- A predicate asserting that two variables in the same context
-- follow one another

data _↷_ : ∀ {Γ σ₁ σ₂} → (x : Var Γ σ₁) → (y : Var Γ σ₂) → Set where
  ↷-z : ∀ {Γ σ₁ σ₂} → _↷_ {(Γ , σ₁) , σ₂} (vs vz) vz
  ↷-s : ∀ {τ Γ σ₁ σ₂} {x : Var Γ σ₁} {y : Var Γ σ₂} →
          x ↷ y → vs {τ = τ} x ↷ vs y

↷-cong : ∀ {Γ σ} {x y : Var Γ σ} →
  x ↷ y → Γ - x ≡ Γ - y

↷-cong ↷-z =
  refl
↷-cong (↷-s {τ = τ} h) =
  ↷-cong h <,< τ

-- vs is injective

vs-inj : ∀ {τ Γ σ} {x y : Var Γ σ} →
  vs {τ = τ} x ≡ vs y → x ≡ y
vs-inj refl = refl

mutual

   /Var/∘<,<∘↷-cong : ∀ {τ Γ σ₁ σ₂} {i j : Var Γ σ₁} (i↷j : i ↷ j)
     {x : Var ((Γ - i) , τ) σ₂} {y : Var ((Γ - j) , τ) σ₂} →
     (vs i) ⇗ˣ x ≡ (vs j) ⇗ˣ y → (↷-cong i↷j <,< τ) /Var/ x ≡ y

   /Var/∘<,<∘↷-cong i↷j {vz} {vz} h =
     /Var/∘vz (↷-cong i↷j)
   /Var/∘<,<∘↷-cong i↷j {vz} {vs y} ()
   /Var/∘<,<∘↷-cong i↷j {vs x} {vz} ()
   /Var/∘<,<∘↷-cong {τ} i↷j {vs x} {vs y} h = begin
     (↷-cong i↷j <,< τ) /Var/ vs x
       ≡⟨ /Var/∘vs (↷-cong i↷j) x ⟩
     vs (↷-cong i↷j /Var/ x)
       ≡⟨ cong vs (/Var/∘↷-cong i↷j (vs-inj h)) ⟩
     vs y
     ∎
     where open ≡-Reasoning

   /Var/∘↷-cong : ∀ {Γ σ₁ σ₂} {i j : Var Γ σ₁} (i↷j : i ↷ j)
     {x : Var (Γ - i) σ₂} {y : Var (Γ - j) σ₂} →
     i ⇗ˣ x ≡ j ⇗ˣ y → ↷-cong i↷j /Var/ x ≡ y

   /Var/∘↷-cong ↷-z {vz} ()
   /Var/∘↷-cong ↷-z {vs x} {vz} ()
   /Var/∘↷-cong ↷-z {vs .y} {vs y} refl =
     refl
   /Var/∘↷-cong (↷-s i↷j) h =
     /Var/∘<,<∘↷-cong i↷j h


postulate

   ƛⁿ∘·β : ∀ {Γ σ τ} (n : Nf Γ (σ ⇒ τ))  →
    ƛⁿ ((vz ⇗ⁿ n) ·β (vz ·η ε)) ≡ n

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

≈βη⇒≡nf (βη-sym {σ} {t₁} {t₂} h) = begin
  nf t₂
    ≡⟨ sym $ ≈βη⇒≡nf h ⟩
  nf t₁
  ∎
  where open ≡-Reasoning

≈βη⇒≡nf (βη-trans {σ} {t₁} {t₂} {t₃} h₁ h₂) = begin
  nf t₁
    ≡⟨ ≈βη⇒≡nf h₁ ⟩
  nf t₂
    ≡⟨ ≈βη⇒≡nf h₂ ⟩
  nf t₃
  ∎
  where open ≡-Reasoning

≈βη⇒≡nf (ƛ-cong {σ} {τ} {t₁} {t₂} h) = begin
  nf (ƛ t₁)
    ≡⟨⟩
  ƛⁿ (nf t₁)
    ≡⟨ cong ƛⁿ (≈βη⇒≡nf h) ⟩
  ƛⁿ (nf t₂)
    ≡⟨⟩
  nf (ƛ t₂)
  ∎
  where open ≡-Reasoning

≈βη⇒≡nf (·-cong {σ} {τ} {t₁} {t₂} {u₁} {u₂} h₁ h₂) = begin
  nf (t₁ · u₁)
    ≡⟨⟩
  nf t₁ ·β nf u₁
    ≡⟨ cong₂ _·β_ (≈βη⇒≡nf h₁) (≈βη⇒≡nf h₂) ⟩
  nf t₂ ·β nf u₂
    ≡⟨⟩
  nf (t₂ · u₂)
  ∎
  where open ≡-Reasoning

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



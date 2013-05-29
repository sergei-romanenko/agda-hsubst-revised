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


mutual

  -- ⇗ⁿ∘⇗ⁿ

  ⇗ⁿ∘⇗ⁿ : ∀ {Γ σ τ ρ} (x : Var Γ σ) (y : Var (Γ - x) τ)
            (t : Nf ((Γ - x) - y) ρ) →
    x ⇗ⁿ (y ⇗ⁿ t) ≡ (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ t))

  ⇗ⁿ∘⇗ⁿ x y (ƛⁿ {σ = σ} t) = begin
    x ⇗ⁿ (y ⇗ⁿ ƛⁿ t)
      ≡⟨⟩
    ƛⁿ (vs x ⇗ⁿ (vs y ⇗ⁿ t))
      ≡⟨ cong ƛⁿ (⇗ⁿ∘⇗ⁿ (vs x) (vs y) t) ⟩
    ƛⁿ (vs (x ⇗ˣ y) ⇗ⁿ (vs (x ⇘ˣ y) ⇗ⁿ ((-∘- x y <,< σ) /Nf/ t)))
      ≡⟨⟩
    (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ ƛⁿ ((-∘- x y <,< σ) /Nf/ t))
      ≡⟨ cong (λ u → (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ u))
              (sym $ /Nf/∘ƛⁿ (-∘- x y) t) ⟩
    (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ ƛⁿ t))
    ∎
    where open ≡-Reasoning
  
  ⇗ⁿ∘⇗ⁿ x y (x′ ·ⁿ ns) = begin
    x ⇗ⁿ (y ⇗ⁿ (x′ ·ⁿ ns))
      ≡⟨⟩
    (x ⇗ˣ (y ⇗ˣ x′)) ·ⁿ (x ⇗ˢ (y ⇗ˢ ns))
      ≡⟨ cong₂ _·ⁿ_ (⇗ˣ∘⇗ˣ x y x′) (⇗ˢ∘⇗ˢ x y ns) ⟩
    ((x ⇗ˣ y) ⇗ˣ ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ x′))) ·ⁿ
      ((x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ ns)))
      ≡⟨⟩
    (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ ((-∘- x y /Var/ x′) ·ⁿ (-∘- x y /Sp/ ns)))
      ≡⟨ cong (λ n → (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ n))
              (sym $ /Nf/∘·ⁿ (-∘- x y) x′ ns) ⟩
    (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ (x′ ·ⁿ ns)))
    ∎
    where open ≡-Reasoning


  -- ⇗ˢ∘⇗ˢ

  ⇗ˢ∘⇗ˢ : ∀ {Γ σ τ ρ α} (x : Var Γ σ) (y : Var (Γ - x) τ)
            (ns : Sp ((Γ - x) - y) ρ α) →
    x ⇗ˢ (y ⇗ˢ ns) ≡
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ ns))

  ⇗ˢ∘⇗ˢ x y [] = begin
    x ⇗ˢ (y ⇗ˢ [])
      ≡⟨⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ [])
      ≡⟨ cong (λ ns → (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ns))
              (sym $ /Sp/∘[] (-∘- x y)) ⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ []))
    ∎
    where open ≡-Reasoning

  ⇗ˢ∘⇗ˢ x y (n ∷ ns) = begin
    x ⇗ˢ (y ⇗ˢ (n ∷ ns))
      ≡⟨⟩
    x ⇗ⁿ (y ⇗ⁿ n) ∷ x ⇗ˢ (y ⇗ˢ ns)
      ≡⟨ cong₂ _∷_ (⇗ⁿ∘⇗ⁿ x y n) (⇗ˢ∘⇗ˢ x y ns) ⟩
    (x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ n)) ∷
        (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ ns))
      ≡⟨⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ((-∘- x y /Nf/ n) ∷ (-∘- x y /Sp/ ns)))
      ≡⟨ cong (λ ns₁ → (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ns₁))
              (sym $ /Sp/∘∷ (-∘- x y) n ns) ⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ (n ∷ ns)))
    ∎
    where open ≡-Reasoning


mutual

  ⇗ˢ∘∷ʳ : ∀ {Γ σ₁ σ₂ τ₁ τ₂} (x : Var Γ σ₁) (ns : Sp (Γ - x) σ₂ (τ₁ ⇒ τ₂)) →
    vs x ⇗ˢ (vz ⇗ˢ ns ∷ʳ vz ·η []) ≡
      vz ⇗ˢ (x ⇗ˢ ns) ∷ʳ vz ·η []

  ⇗ˢ∘∷ʳ x [] = cong (λ n → n ∷ []) (⇗ⁿ∘·η (vs x) vz [])
  ⇗ˢ∘∷ʳ x (n ∷ ns) = begin
    vs x ⇗ˢ (vz ⇗ˢ (n ∷ ns) ∷ʳ vz ·η [])
      ≡⟨⟩
    vs x ⇗ⁿ (vz ⇗ⁿ n) ∷ vs x ⇗ˢ (vz ⇗ˢ ns ∷ʳ vz ·η [])
      ≡⟨ cong₂ _∷_ (sym $ ⇗ⁿ∘⇗ⁿ vz x n) (⇗ˢ∘∷ʳ x ns) ⟩
    vz ⇗ⁿ (x ⇗ⁿ n) ∷ (vz ⇗ˢ (x ⇗ˢ ns) ∷ʳ vz ·η [])
      ≡⟨⟩
    vz ⇗ˢ (x ⇗ˢ (n ∷ ns)) ∷ʳ vz ·η []
    ∎
    where open ≡-Reasoning


  ⇗ⁿ∘·η : ∀ {τ Γ σ₁ σ₂} (x : Var Γ σ₁)
            (y : Var (Γ - x) σ₂) (ns : Sp (Γ - x) σ₂ τ) →
    x ⇗ⁿ (y ·η ns) ≡ (x ⇗ˣ y) ·η (x ⇗ˢ ns)

  ⇗ⁿ∘·η {○} x y ns = refl
  ⇗ⁿ∘·η {τ₁ ⇒ τ₂} x y ns = begin
    x ⇗ⁿ (y ·η ns)
      ≡⟨⟩
    ƛⁿ (vs x ⇗ⁿ (vs y ·η ((vz ⇗ˢ ns) ∷ʳ (vz ·η []))))
      ≡⟨ cong ƛⁿ (⇗ⁿ∘·η (vs x) (vs y) ((vz ⇗ˢ ns) ∷ʳ (vz ·η []))) ⟩
    ƛⁿ (vs (x ⇗ˣ y) ·η (vs x ⇗ˢ ((vz ⇗ˢ ns) ∷ʳ (vz ·η []))))
      ≡⟨ cong (λ u → ƛⁿ (vs (x ⇗ˣ y) ·η u))
              (⇗ˢ∘∷ʳ x ns) ⟩
    ƛⁿ (vs (x ⇗ˣ y) ·η (vz ⇗ˢ (x ⇗ˢ ns) ∷ʳ vz ·η []))
      ≡⟨⟩
    (x ⇗ˣ y) ·η (x ⇗ˢ ns)
    ∎
    where open ≡-Reasoning

postulate

  ⇗ⁿ∘·β : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ)
            (n₁ : Nf (Γ - x) (τ₁ ⇒ τ₂)) (n₂ : Nf (Γ - x) τ₁) →
    x ⇗ⁿ (n₁ ·β n₂) ≡ (x ⇗ⁿ n₁) ·β (x ⇗ⁿ n₂)

  ⇗ⁿ∘◇ : ∀ {Γ σ τ ρ} (x : Var Γ σ) (n : Nf (Γ - x) τ) 
           (ns : Sp (Γ - x) τ ρ) →
    x ⇗ⁿ (n ◇ ns) ≡ (x ⇗ⁿ n) ◇ (x ⇗ˢ ns)


-- nf∘⇗

nf∘⇗ : ∀ {Γ σ τ} (x : Var Γ σ) (t : Tm (Γ - x) τ) →
  nf (x ⇗ t) ≡ x ⇗ⁿ (nf t)

nf∘⇗ x (var x′) =
  sym $ ⇗ⁿ∘·η x x′ []
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

{-
postulate

  ⇗ⁿ∘[≔] : ∀ {Γ σ σ′ τ} (x : Var Γ σ)
             (n : Nf (Γ - x) τ) (u : Nf (Γ - x) σ′) →
    x ⇗ⁿ (n [ vz ≔ u ]) ≡ (vs x ⇗ⁿ n) [ vz ≔ x ⇗ⁿ u ]
-}

-- Normalization and substitution commute.

postulate

  nf∘[≔] : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) (u : Tm (Γ - x) σ) →
    (nf t) [ x ≔ nf u ] ≡ nf (substTm t x u)



-- x ↷ y means that two variables are in the same context and vs y = x .

data _↷_ : ∀ {Γ σ₁ σ₂} → (x : Var Γ σ₁) → (y : Var Γ σ₂) → Set where
  ↷-z : ∀ {Γ σ₁ σ₂} → _↷_ {(Γ , σ₁) , σ₂} (vs vz) vz
  ↷-s : ∀ {τ Γ σ₁ σ₂} {x : Var Γ σ₁} {y : Var Γ σ₂} →
          x ↷ y → vs {τ = τ} x ↷ vs y

-- ↷-cong

↷-cong : ∀ {Γ σ} {x y : Var Γ σ} →
  x ↷ y → Γ - x ≡ Γ - y

↷-cong ↷-z =
  refl
↷-cong (↷-s {τ = τ} h) =
  ↷-cong h <,< τ

-- vs-inj
-- vs is injective

vs-inj : ∀ {τ Γ σ} {x y : Var Γ σ} →
  vs {τ = τ} x ≡ vs y → x ≡ y
vs-inj refl = refl

-- ⇗ˣ-inj
-- ⇗ˣ is injective

⇗ˣ-inj : ∀ {Γ σ τ} (i : Var Γ σ) (x y : Var (Γ - i) τ) →
  i ⇗ˣ x ≡ i ⇗ˣ y → x ≡ y

⇗ˣ-inj vz x y h = vs-inj h
⇗ˣ-inj (vs i) vz vz h = refl
⇗ˣ-inj (vs i) vz (vs y) ()
⇗ˣ-inj (vs i) (vs x) vz ()
⇗ˣ-inj (vs i) (vs x) (vs y) h =
  cong vs (⇗ˣ-inj i x y (vs-inj h))


mutual

  -- /Var/∘<,<∘↷-cong

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

  -- /Var/∘↷-cong

  /Var/∘↷-cong : ∀ {Γ σ₁ σ₂} {i j : Var Γ σ₁} (i↷j : i ↷ j)
    {x : Var (Γ - i) σ₂} {y : Var (Γ - j) σ₂} →
    i ⇗ˣ x ≡ j ⇗ˣ y → (↷-cong i↷j) /Var/ x ≡ y

  /Var/∘↷-cong ↷-z {vz} ()
  /Var/∘↷-cong ↷-z {vs x} {vz} ()
  /Var/∘↷-cong ↷-z {vs .y} {vs y} refl =
    refl
  /Var/∘↷-cong (↷-s i↷j) h =
    /Var/∘<,<∘↷-cong i↷j h

{-
postulate

  ⇗ⁿ∘[≔] : ∀ {Γ σ σ′ τ} (x : Var Γ σ)
             (n : Nf (Γ - x) τ) (u : Nf (Γ - x) σ′) →
    x ⇗ⁿ (n [ vz ≔ u ]) ≡ (vs x ⇗ⁿ n) [ vz ≔ x ⇗ⁿ u ]
-}


-- _++ˢ_

infixr 5 _++ˢ_

_++ˢ_ : ∀ {Γ σ₁ σ₂ σ₃} (ns₁ : Sp Γ σ₁ σ₂) (ns₂ : Sp Γ σ₂ σ₃) → Sp Γ σ₁ σ₃

[] ++ˢ ns₂ = ns₂
(n ∷ ns₁) ++ˢ ns₂ = n ∷ (ns₁ ++ˢ ns₂)

-- ++ˢε

++ˢε : ∀ {Γ σ τ} (ns : Sp Γ σ τ) → ns ++ˢ [] ≡ ns

++ˢε [] = refl
++ˢε (n ∷ ns) = cong (λ u → n ∷ u) (++ˢε ns)

-- ++ˢ∘∷

++ˢ∘∷ : ∀ {Γ σ₁ σ₂ σ₃ τ}
           (ns₁ : Sp Γ σ₁ (τ ⇒ σ₂)) (n : Nf Γ τ) (ns₂ : Sp Γ σ₂ σ₃) →
  ns₁ ++ˢ (n ∷ ns₂) ≡ (ns₁ ∷ʳ n) ++ˢ ns₂

++ˢ∘∷ [] n ns₂ = refl
++ˢ∘∷ (n′ ∷ ns₁) n ns₂ = cong (λ u → n′ ∷ u) (++ˢ∘∷ ns₁ n ns₂)

-- ◇∘∷ʳ

◇∘∷ʳ : ∀ {Γ τ₁ τ₂ σ} (ns : Sp Γ τ₁ (τ₂ ⇒ σ)) (n : Nf Γ τ₂)
         (u : Nf Γ τ₁) →
  u ◇ (ns ∷ʳ n) ≡ (u ◇ ns) ·β  n

◇∘∷ʳ [] n u = refl
◇∘∷ʳ (n′ ∷ ns) n u =
  ◇∘∷ʳ ns n (u ·β n′)

-- <≔>∘∷ʳ

<≔>∘∷ʳ : ∀ {Γ τ₁ τ₂ τ₃ σ} (ns : Sp Γ τ₁ (τ₂ ⇒ τ₃)) (n : Nf Γ τ₂)
           (x : Var Γ σ) (u : Nf (Γ - x) σ) →
  (ns ∷ʳ n) < x ≔ u > ≡ (ns < x ≔ u >) ∷ʳ (n [ x ≔ u ])

<≔>∘∷ʳ [] n x u = refl
<≔>∘∷ʳ (n′ ∷ ns) n x u =
  cong (_∷_ (n′ [ x ≔ u ])) (<≔>∘∷ʳ ns n x u)


postulate

  [≔]∘·η∘⇗ˣ : ∀ {Γ σ τ₁ τ₂}
    (x : Var Γ σ) (ns : Sp Γ τ₁ τ₂) (u : Nf (Γ - x) σ) (y : Var (Γ - x) τ₁) →
    ((x ⇗ˣ y) ·η ns) [ x ≔ u ] ≡ y ·η (ns < x ≔ u >)

  <≔>∘∷ʳ∘⇗ˢ : ∀ {Γ τ₁ τ₂ σ τ₃}
    (x : Var Γ σ) (ns : Sp Γ τ₁ (τ₂ ⇒ τ₃)) (u : Nf (Γ - x) σ) →
    (vz ⇗ˢ ns ∷ʳ vz ·η []) < vs x ≔ (vz ⇗ⁿ u) > ≡
      vz ⇗ˢ (ns < x ≔ u >) ∷ʳ vz ·η []

postulate

  ⇗ˢ∘<≔>-id : ∀ {Γ σ τ₁ τ₂}
    (x : Var Γ σ) (ns : Sp (Γ - x) τ₁ τ₂) (u : Nf (Γ - x) σ) →
    (x ⇗ˢ ns) < x ≔ u > ≡ ns


mutual

  -- ↷/Nf/

  ↷/Nf/ : ∀ {Γ σ τ} {i j : Var Γ σ} (i↷j : i ↷ j)
              (n : Nf (Γ - i) τ) (x : Var (Γ - j) σ) →
              i ⇗ˣ ((sym $ ↷-cong i↷j) /Var/ x) ≡ j →
    (↷-cong i↷j) /Nf/ n ≡ (i ⇗ⁿ n) [ j ≔ x ·η [] ]

  ↷/Nf/ {i = i} {j = j} i↷j (ƛⁿ {σ = σ} n) x h = begin
    ↷-cong i↷j /Nf/ ƛⁿ n
      ≡⟨ /Nf/∘ƛⁿ (↷-cong i↷j) n ⟩
    ƛⁿ ((↷-cong i↷j <,< σ) /Nf/ n)
      ≡⟨⟩
    ƛⁿ ((↷-cong (↷-s i↷j)) /Nf/ n)
      ≡⟨ cong ƛⁿ (↷/Nf/ (↷-s i↷j) n (vs x) helper) ⟩
    ƛⁿ ((vs i ⇗ⁿ n) [ vs j ≔ vs x ·η [] ])
      ≡⟨ cong (λ u → ƛⁿ ((vs i ⇗ⁿ n) [ vs j ≔ u ])) (sym $ ⇗ⁿ∘·η vz x []) ⟩
    ƛⁿ ((vs i ⇗ⁿ n) [ vs j ≔ vz ⇗ⁿ (x ·η []) ])
      ≡⟨⟩
    (i ⇗ⁿ ƛⁿ n) [ j ≔ x ·η [] ]
    ∎
    where
    open ≡-Reasoning
    helper = begin
      vs i ⇗ˣ ((sym $ ↷-cong (↷-s i↷j)) /Var/ vs x)
        ≡⟨⟩
      vs i ⇗ˣ (sym (↷-cong i↷j <,< σ) /Var/ vs x)
        ≡⟨ cong (λ p → vs i ⇗ˣ (p /Var/ vs x))
                (sym $ sym∘<,< (↷-cong i↷j) σ) ⟩
      vs i ⇗ˣ ((sym (↷-cong i↷j) <,< σ) /Var/ vs x)
        ≡⟨ cong (λ u → vs i ⇗ˣ u) (/Var/∘vs (sym (↷-cong i↷j)) x) ⟩
      vs (i ⇗ˣ (sym (↷-cong i↷j) /Var/ x))
        ≡⟨ cong vs h ⟩
      vs j
      ∎

  ↷/Nf/ {i = i} {j = j} i↷j (x′ ·ⁿ ns) x h with i ⇗ˣ x′ | inspect (_⇗ˣ_ i) x′
  ... | l | [ l≡ ] with varDiff j l

  ↷/Nf/ {i = i} i↷j (x′ ·ⁿ ns) x h | l | [ l≡ ] | ⟳ˣ = begin
    ↷-cong i↷j /Nf/ (x′ ·ⁿ ns)
      ≡⟨ /Nf/∘·ⁿ (↷-cong i↷j) x′ ns ⟩
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ cong₂ _·ⁿ_ (sym $ helper) (↷/Sp/ i↷j ns x h) ⟩
    x ·ⁿ ((i ⇗ˢ ns) < l ≔ x ·η [] >)
      ≡⟨ sym $ ◇∘·η x [] ((i ⇗ˢ ns) < l ≔ x ·η [] >) ⟩
    (x ·η []) ◇ ((i ⇗ˢ ns) < l ≔ x ·η [] >)
    ∎
    where
    open ≡-Reasoning
    p1 : i ⇗ˣ x′ ≡ i ⇗ˣ (sym (↷-cong i↷j) /Var/ x)
    p1 = trans l≡ (sym h)
    p2 : x′ ≡ sym (↷-cong i↷j) /Var/ x
    p2 =  ⇗ˣ-inj i x′ (sym (↷-cong i↷j) /Var/ x) p1
    helper : x ≡ ↷-cong i↷j /Var/ x′
    helper = /Var/∘sym x′ x (↷-cong i↷j) p2
  

  ↷/Nf/ {i = i} i↷j (x′ ·ⁿ ns) x h | .(j ⇗ˣ v) | [ l≡ ] | j ↗ˣ v = begin
    ↷-cong i↷j /Nf/ (x′ ·ⁿ ns)
      ≡⟨ /Nf/∘·ⁿ (↷-cong i↷j) x′ ns ⟩
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ cong₂ _·ⁿ_ (/Var/∘↷-cong i↷j l≡) (↷/Sp/ i↷j ns x h) ⟩
    v ·ⁿ ((i ⇗ˢ ns) < j ≔ x ·η [] >)
    ∎
    where open ≡-Reasoning

  -- ↷/Sp/

  ↷/Sp/ : ∀ {Γ σ τ ρ} {i j : Var Γ σ} (i↷j : i ↷ j)
            (ns : Sp (Γ - i) ρ τ) (x : Var (Γ - j) σ) →
            i ⇗ˣ ((sym $ ↷-cong i↷j) /Var/ x) ≡ j →
    ↷-cong i↷j /Sp/ ns ≡ (i ⇗ˢ ns) < j ≔ (x ·η []) >

  ↷/Sp/ i↷j [] x h =
    /Sp/∘[] (↷-cong i↷j)

  ↷/Sp/ {i = i} {j = j} i↷j (n ∷ ns) x h = begin
    ↷-cong i↷j /Sp/ (n ∷ ns)
      ≡⟨ /Sp/∘∷ (↷-cong i↷j) n ns ⟩
    (↷-cong i↷j /Nf/ n) ∷ (↷-cong i↷j /Sp/ ns)
      ≡⟨ cong₂ _∷_ (↷/Nf/ i↷j n x h) (↷/Sp/ i↷j ns x h) ⟩
    (i ⇗ⁿ n) [ j ≔ x ·η [] ] ∷ (i ⇗ˢ ns) < j ≔ x ·η [] >
      ≡⟨⟩
    (i ⇗ˢ (n ∷ ns)) < j ≔ x ·η [] >
    ∎
    where open ≡-Reasoning


  -- ◇∘·η

  ◇∘·η : ∀ {Γ σ τ} (x : Var Γ σ) (ns₁ : Sp Γ σ τ) (ns₂ : Sp Γ τ ○) →
      (x ·η ns₁) ◇ ns₂ ≡ x ·ⁿ (ns₁ ++ˢ ns₂)

  ◇∘·η x ns₁ [] = begin
    (x ·η ns₁) ◇ []
      ≡⟨⟩
    x ·ⁿ ns₁
      ≡⟨ cong (_·ⁿ_ x) (sym $ ++ˢε ns₁) ⟩
    x ·ⁿ (ns₁ ++ˢ [])
    ∎
    where open ≡-Reasoning

  ◇∘·η x ns₁ (n ∷ ns₂) = begin
    (x ·η ns₁) ◇ (n ∷ ns₂)
      ≡⟨⟩
    ((vs x ·η (vz ⇗ˢ ns₁ ∷ʳ vz ·η [])) [ vz ≔ n ]) ◇ ns₂
      ≡⟨ cong (λ ns → ns ◇ ns₂)
              ([≔]∘·η∘⇗ˣ vz (vz ⇗ˢ ns₁ ∷ʳ vz ·η []) n x) ⟩
    (x ·η ((vz ⇗ˢ ns₁ ∷ʳ vz ·η []) < vz ≔ n >)) ◇ ns₂
      ≡⟨ cong (λ ns → (x ·η ns) ◇ ns₂)
              (<≔>∘∷ʳ (vz ⇗ˢ ns₁) (vz ·η []) vz n) ⟩
    (x ·η (vz ⇗ˢ ns₁ < vz ≔ n > ∷ʳ (vz ·η []) [ vz ≔ n ])) ◇ ns₂
      ≡⟨ cong₂ (λ us u → (x ·η (us ∷ʳ u)) ◇ ns₂)
               (⇗ˢ∘<≔>-id vz ns₁ n) ([≔]∘·η vz [] n) ⟩
    (x ·η (ns₁ ∷ʳ n)) ◇ ns₂
      ≡⟨ ◇∘·η x (ns₁ ∷ʳ n) ns₂ ⟩
    x ·ⁿ ((ns₁ ∷ʳ n) ++ˢ ns₂)
      ≡⟨ cong (_·ⁿ_ x) (sym $ ++ˢ∘∷ ns₁ n ns₂) ⟩
    x ·ⁿ (ns₁ ++ˢ (n ∷ ns₂))
    ∎
    where open ≡-Reasoning

  -- [≔]∘·η

  [≔]∘·η : ∀ {τ Γ σ} (x : Var Γ σ) (ns : Sp Γ σ τ) (u : Nf (Γ - x) σ) →
    (x ·η ns) [ x ≔ u ] ≡ u ◇ (ns < x ≔ u >)

  [≔]∘·η {○} x ns u rewrite varDiff-⟳ˣ x = refl

  [≔]∘·η {τ₁ ⇒ τ₂} x ns u = begin
    (x ·η ns) [ x ≔ u ]
      ≡⟨⟩
    ƛⁿ ((vs x ·η (vz ⇗ˢ ns ∷ʳ vz ·η [])) [ vs x ≔ vz ⇗ⁿ u ])
      ≡⟨ cong ƛⁿ ([≔]∘·η (vs x) ((vz ⇗ˢ ns) ∷ʳ (vz ·η [])) (vz ⇗ⁿ u)) ⟩
    ƛⁿ (vz ⇗ⁿ u ◇ ((vz ⇗ˢ ns ∷ʳ vz ·η []) < vs x ≔ vz ⇗ⁿ u >))
      ≡⟨ cong (λ us → ƛⁿ ((vz ⇗ⁿ u) ◇ us))
              (<≔>∘∷ʳ∘⇗ˢ x ns u) ⟩
    ƛⁿ (vz ⇗ⁿ u ◇ (vz ⇗ˢ (ns < x ≔ u >) ∷ʳ vz ·η []))
      ≡⟨ cong ƛⁿ (◇∘∷ʳ (vz ⇗ˢ (ns < x ≔ u >)) (vz ·η []) (vz ⇗ⁿ u)) ⟩
    ƛⁿ ((vz ⇗ⁿ u ◇ vz ⇗ˢ (ns < x ≔ u >)) ·β (vz ·η []))
      ≡⟨ cong (λ n → ƛⁿ (n ·β (vz ·η []))) (sym $ ⇗ⁿ∘◇ vz u (ns < x ≔ u >)) ⟩
    ƛⁿ (vz ⇗ⁿ (u ◇ (ns < x ≔ u >)) ·β (vz ·η []))
      ≡⟨ ƛⁿ∘·β (u ◇ (ns < x ≔ u >)) ⟩
    u ◇ (ns < x ≔ u >)
    ∎
    where open ≡-Reasoning


  -- ƛⁿ∘·β

  ƛⁿ∘·β : ∀ {Γ σ τ} (n : Nf Γ (σ ⇒ τ))  →
    ƛⁿ ((vz ⇗ⁿ n) ·β (vz ·η [])) ≡ n

  ƛⁿ∘·β {Γ} {σ} {τ} (ƛⁿ n) = begin
    ƛⁿ ((vz ⇗ⁿ ƛⁿ n) ·β (vz ·η []))
      ≡⟨⟩
    ƛⁿ (vs vz ⇗ⁿ n [ vz ≔ vz ·η [] ])
      ≡⟨ cong ƛⁿ (sym $ ↷/Nf/ ↷-z n vz (vz ≡ vz ∋ refl)) ⟩
    ƛⁿ n
    ∎
    where open ≡-Reasoning


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
  ƛⁿ (nf (vz ⇗ t) ·β (vz ·η []))
    ≡⟨ cong (λ n → ƛⁿ (n ·β (vz ·η []))) (nf∘⇗ vz t) ⟩
  ƛⁿ ((vz ⇗ⁿ nf t) ·β (vz ·η []))
    ≡⟨ ƛⁿ∘·β (nf t) ⟩
  nf t
  ∎
  where open ≡-Reasoning

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
    vs x ⇗ˢ (vz ⇗ˢ ns ∷ʳ vz ·η []) ≡ vz ⇗ˢ (x ⇗ˢ ns) ∷ʳ vz ·η []

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


mutual

  -- ⇗ⁿ∘·β

  ⇗ⁿ∘·β : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ)
            (n₁ : Nf (Γ - x) (τ₁ ⇒ τ₂)) (n₂ : Nf (Γ - x) τ₁) →
    x ⇗ⁿ (n₁ ·β n₂) ≡ (x ⇗ⁿ n₁) ·β (x ⇗ⁿ n₂)

  ⇗ⁿ∘·β x (ƛⁿ n₁) n₂ = /Nf/∘[≔] (vs x) vz n₂ n₁

  -- ⇗ⁿ∘◇

  ⇗ⁿ∘◇ : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ) (n : Nf (Γ - x) τ₁) 
           (ns : Sp (Γ - x) τ₁ τ₂) →
    x ⇗ⁿ (n ◇ ns) ≡ (x ⇗ⁿ n) ◇ (x ⇗ˢ ns)

  ⇗ⁿ∘◇ x n [] = refl
  ⇗ⁿ∘◇ x n (_∷_ {σ = σ} {τ₁} {τ₂} n′ ns) = begin
    x ⇗ⁿ (n ◇ (n′ ∷ ns))
      ≡⟨⟩
    x ⇗ⁿ ((n ·β n′) ◇ ns)
      ≡⟨ ⇗ⁿ∘◇ x (n ·β n′) ns ⟩
    x ⇗ⁿ (n ·β n′) ◇ x ⇗ˢ ns
      ≡⟨ cong₂ _◇_ (⇗ⁿ∘·β x n n′) (begin x ⇗ˢ ns ∎) ⟩
    (x ⇗ⁿ n ·β x ⇗ⁿ n′) ◇ x ⇗ˢ ns
      ≡⟨⟩
    x ⇗ⁿ n ◇ x ⇗ˢ (n′ ∷ ns)
    ∎
    where open ≡-Reasoning

  -- /Nf/∘[≔]

  /Nf/∘[≔] : ∀ {Γ σ₁ σ₂ τ} (y : Var Γ σ₁)
      (x : Var (Γ - y) σ₂) (u : Nf ((Γ - y) - x) σ₂) (n : Nf (Γ - y) τ) →
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ (n [ x ≔ u ])) ≡
      (y ⇗ⁿ n) [ (y ⇗ˣ x) ≔ ((y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u)) ]

  /Nf/∘[≔] y x u (ƛⁿ {σ = σ} {τ = τ} n) = begin
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ (ƛⁿ n [ x ≔ u ]))
      ≡⟨⟩
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ ƛⁿ (n [ vs x ≔ vz ⇗ⁿ u ]))
      ≡⟨ cong (_⇗ⁿ_ (y ⇘ˣ x)) (/Nf/∘ƛⁿ (-∘- y x) (n [ vs x ≔ vz ⇗ⁿ u ])) ⟩
    ƛⁿ (vs (y ⇘ˣ x) ⇗ⁿ
           ((-∘- y x <,< σ) /Nf/ (n [ vs x ≔ vz ⇗ⁿ u ])))
      ≡⟨ cong ƛⁿ (/Nf/∘[≔] (vs y) (vs x) (vz ⇗ⁿ u) n) ⟩
    ƛⁿ ((vs y ⇗ⁿ n) [ vs (y ⇗ˣ x) ≔
          vs (y ⇘ˣ x) ⇗ⁿ ((-∘- y x <,< σ) /Nf/ (vz ⇗ⁿ u)) ])
      ≡⟨ cong (λ n′ → ƛⁿ (vs y ⇗ⁿ n [ vs (y ⇗ˣ x) ≔ vs (y ⇘ˣ x) ⇗ⁿ n′ ]))
              (/Nf/∘<,< (-∘- y x) u) ⟩
    ƛⁿ ((vs y ⇗ⁿ n) [ vs (y ⇗ˣ x) ≔
            vs (y ⇘ˣ x) ⇗ⁿ (vz ⇗ⁿ (-∘- y x /Nf/ u)) ])
      ≡⟨ cong (λ n′ → ƛⁿ (vs y ⇗ⁿ n [ vs (y ⇗ˣ x) ≔ n′ ]))
              (⇗ⁿ∘⇗ⁿ (vs (y ⇘ˣ x)) vz (-∘- y x /Nf/ u)) ⟩
    ƛⁿ ((vs y ⇗ⁿ n) [ vs (y ⇗ˣ x) ≔ vz ⇗ⁿ ((y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u)) ])
      ≡⟨⟩
    (y ⇗ⁿ ƛⁿ n) [ y ⇗ˣ x ≔ (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) ]
    ∎
    where open ≡-Reasoning

  /Nf/∘[≔] y x u (v ·ⁿ ns) with varDiff x v

  /Nf/∘[≔] y x u (.x ·ⁿ ns) | ⟳ˣ
    rewrite varDiff-⟳ˣ (y ⇗ˣ x) = begin
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u ◇ (ns < x ≔ u >))
      ≡⟨ cong (_⇗ⁿ_ (y ⇘ˣ x)) (/Nf/∘◇ (-∘- y x) u (ns < x ≔ u >)) ⟩
    (y ⇘ˣ x) ⇗ⁿ ((-∘- y x /Nf/ u) ◇ (-∘- y x /Sp/ ns < x ≔ u >))
      ≡⟨ ⇗ⁿ∘◇ (y ⇘ˣ x) (-∘- y x /Nf/ u) (-∘- y x /Sp/ ns < x ≔ u >) ⟩
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) ◇ (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ ns < x ≔ u >)
      ≡⟨ cong₂ _◇_ refl (/Sp/∘<≔> y x u ns) ⟩
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) ◇
      (y ⇗ˢ ns < y ⇗ˣ x ≔ (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) >)
    ∎
    where open ≡-Reasoning

  /Nf/∘[≔] y x u (.(x ⇗ˣ v) ·ⁿ ns) | .x ↗ˣ v
    rewrite ⇗ˣ∘⇗ˣ y x v
          | varDiff-↗ˣ (y ⇗ˣ x) ((y ⇘ˣ x) ⇗ˣ (-∘- y x /Var/ v))
          | /Nf/∘·ⁿ (-∘- y x) v (ns < x ≔ u >)
          | /Sp/∘<≔> y x u ns
    = refl

  -- /Sp/∘<≔>

  /Sp/∘<≔> : ∀ {Γ σ₁  σ₂ τ₁ τ₂} (y : Var Γ σ₁)
    (x : Var (Γ - y) σ₂) (u : Nf ((Γ - y) - x) σ₂) (ns : Sp (Γ - y) τ₁ τ₂) →
    (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ (ns < x ≔ u >)) ≡
      (y ⇗ˢ ns) < (y ⇗ˣ x) ≔ ((y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u)) >

  /Sp/∘<≔> y x u [] = begin
    (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ [] < x ≔ u >)
      ≡⟨⟩
    (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ [])
      ≡⟨ cong (_⇗ˢ_ (y ⇘ˣ x)) (/Sp/∘[] (-∘- y x)) ⟩
    []
      ≡⟨⟩
    y ⇗ˢ [] < y ⇗ˣ x ≔ (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) >
    ∎
    where open ≡-Reasoning

  /Sp/∘<≔> y x u (n ∷ ns) = begin
    (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ (n ∷ ns) < x ≔ u >)
      ≡⟨⟩
    (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ (n [ x ≔ u ] ∷ ns < x ≔ u >))
      ≡⟨ cong (_⇗ˢ_ (y ⇘ˣ x))
              (/Sp/∘∷ (-∘- y x) (n [ x ≔ u ]) (ns < x ≔ u >)) ⟩
    (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ n [ x ≔ u ]) ∷
      (y ⇘ˣ x) ⇗ˢ (-∘- y x /Sp/ ns < x ≔ u >)
      ≡⟨ cong₂ _∷_
               (/Nf/∘[≔] y x u n) (/Sp/∘<≔> y x u ns) ⟩
    y ⇗ⁿ n [ y ⇗ˣ x ≔ (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) ] ∷
      y ⇗ˢ ns < y ⇗ˣ x ≔ (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) >
      ≡⟨⟩
    y ⇗ˢ (n ∷ ns) < y ⇗ˣ x ≔ (y ⇘ˣ x) ⇗ⁿ (-∘- y x /Nf/ u) >
    ∎
    where open ≡-Reasoning


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


mutual

  [≔]∘·η∘⇗ˣ : ∀ {τ₂ Γ σ τ₁}
    (x : Var Γ σ) (u : Nf (Γ - x) σ) (y : Var (Γ - x) τ₁) (ns : Sp Γ τ₁ τ₂) →
    ((x ⇗ˣ y) ·η ns) [ x ≔ u ] ≡ y ·η (ns < x ≔ u >)

  [≔]∘·η∘⇗ˣ {○} x u y ns
    rewrite varDiff-↗ˣ x y = refl
  [≔]∘·η∘⇗ˣ {τ ⇒ τ′} x u y ns = begin
    ƛⁿ ((vs (x ⇗ˣ y) ·η (vz ⇗ˢ ns ∷ʳ vz ·η [])) [ vs x ≔ vz ⇗ⁿ u ])
      ≡⟨ cong ƛⁿ ([≔]∘·η∘⇗ˣ (vs x) (vz ⇗ⁿ u) (vs y) (vz ⇗ˢ ns ∷ʳ vz ·η [])) ⟩
    ƛⁿ (vs y ·η ((vz ⇗ˢ ns ∷ʳ vz ·η []) < vs x ≔ vz ⇗ⁿ u >))
      ≡⟨ cong (λ us → ƛⁿ (vs y ·η us)) (<≔>∘∷ʳ∘⇗ˢ x u ns) ⟩
    ƛⁿ (vs y ·η (vz ⇗ˢ (ns < x ≔ u >) ∷ʳ vz ·η []))
    ∎
    where open ≡-Reasoning

  <≔>∘∷ʳ∘⇗ˢ : ∀ {Γ τ₁ τ₂ σ τ₃}
    (x : Var Γ σ) (u : Nf (Γ - x) σ) (ns : Sp Γ τ₁ (τ₂ ⇒ τ₃)) →
    (vz ⇗ˢ ns ∷ʳ vz ·η []) < vs x ≔ (vz ⇗ⁿ u) > ≡
      vz ⇗ˢ (ns < x ≔ u >) ∷ʳ vz ·η []

  <≔>∘∷ʳ∘⇗ˢ x u ns = begin
    (vz ⇗ˢ ns ∷ʳ vz ·η []) < vs x ≔ vz ⇗ⁿ u >
      ≡⟨ <≔>∘∷ʳ (vz ⇗ˢ ns) (vz ·η []) (vs x) (vz ⇗ⁿ u) ⟩
    vz ⇗ˢ ns < vs x ≔ vz ⇗ⁿ u > ∷ʳ (vz ·η []) [ vs x ≔ vz ⇗ⁿ u ]
      ≡⟨ cong₂ _∷ʳ_ (sym $ /Sp/∘<≔> vz x u ns)
                    ([≔]∘·η∘⇗ˣ (vs x) (vz ⇗ⁿ u) vz []) ⟩
    vz ⇗ˢ (ns < x ≔ u >) ∷ʳ vz ·η []
    ∎
    where open ≡-Reasoning

{-
postulate

  ⇗ⁿ∘[≔] : ∀ {Γ σ σ′ τ} (x : Var Γ σ)
             (n : Nf (Γ - x) τ) (u : Nf (Γ - x) σ′) →
    x ⇗ⁿ (n [ vz ≔ u ]) ≡ (vs x ⇗ⁿ n) [ vz ≔ x ⇗ⁿ u ]

  ⇗ⁿ∘[≔] : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ)
             (n₁  : Nf ((Γ - x) , τ₁) τ₂) (n₂  : Nf (Γ - x) τ₁) →
    x ⇗ⁿ (n₁ [ vz ≔ n₂ ]) ≡ (vs x ⇗ⁿ n₁) [ vz ≔ x ⇗ⁿ n₂ ]
-}


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

  -- ↷/Var/∘<,<

  ↷/Var/∘<,< : ∀ {τ Γ σ₁ σ₂} {i j : Var Γ σ₁} (i↷j : i ↷ j)
    {x : Var ((Γ - i) , τ) σ₂} {y : Var ((Γ - j) , τ) σ₂} →
    (vs i) ⇗ˣ x ≡ (vs j) ⇗ˣ y → (↷-cong i↷j <,< τ) /Var/ x ≡ y

  ↷/Var/∘<,< i↷j {vz} {vz} h =
    /Var/∘vz (↷-cong i↷j)
  ↷/Var/∘<,< i↷j {vz} {vs y} ()
  ↷/Var/∘<,< i↷j {vs x} {vz} ()
  ↷/Var/∘<,< {τ} i↷j {vs x} {vs y} h = begin
    (↷-cong i↷j <,< τ) /Var/ vs x
      ≡⟨ /Var/∘vs (↷-cong i↷j) x ⟩
    vs (↷-cong i↷j /Var/ x)
      ≡⟨ cong vs (↷/Var/ i↷j (vs-inj h)) ⟩
    vs y
    ∎
    where open ≡-Reasoning

  -- ↷/Var/

  ↷/Var/ : ∀ {Γ σ₁ σ₂} {i j : Var Γ σ₁} (i↷j : i ↷ j)
    {x : Var (Γ - i) σ₂} {y : Var (Γ - j) σ₂} →
    i ⇗ˣ x ≡ j ⇗ˣ y → (↷-cong i↷j) /Var/ x ≡ y

  ↷/Var/ ↷-z {vz} ()
  ↷/Var/ ↷-z {vs x} {vz} ()
  ↷/Var/ ↷-z {vs .y} {vs y} refl =
    refl
  ↷/Var/ (↷-s i↷j) h =
    ↷/Var/∘<,< i↷j h


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



mutual

  -- ⇗ⁿ∘[≔]-id

  ⇗ⁿ∘[≔]-id : ∀ {Γ σ τ}
    (x : Var Γ σ) (u : Nf (Γ - x) σ) (n : Nf (Γ - x) τ) →
    x ⇗ⁿ n [ x ≔ u ] ≡ n

  ⇗ⁿ∘[≔]-id x u (ƛⁿ n) = begin
    x ⇗ⁿ ƛⁿ n [ x ≔ u ]
      ≡⟨⟩
    ƛⁿ (vs x ⇗ⁿ n [ vs x ≔ vz ⇗ⁿ u ])
      ≡⟨ cong ƛⁿ (⇗ⁿ∘[≔]-id (vs x) (vz ⇗ⁿ u) n) ⟩
    ƛⁿ n
    ∎
    where open ≡-Reasoning

  ⇗ⁿ∘[≔]-id x u (x′ ·ⁿ ns) rewrite varDiff-↗ˣ x x′ = begin
    x′ ·ⁿ (x ⇗ˢ ns < x ≔ u >)
      ≡⟨ cong₂ _·ⁿ_ refl (⇗ˢ∘<≔>-id x u ns) ⟩
    x′ ·ⁿ ns
    ∎
    where open ≡-Reasoning

  -- ⇗ˢ∘<≔>-id

  ⇗ˢ∘<≔>-id : ∀ {Γ σ τ₁ τ₂}
    (x : Var Γ σ) (u : Nf (Γ - x) σ) (ns : Sp (Γ - x) τ₁ τ₂) →
    (x ⇗ˢ ns) < x ≔ u > ≡ ns

  ⇗ˢ∘<≔>-id x u [] = refl

  ⇗ˢ∘<≔>-id x u (n ∷ ns) = begin
    x ⇗ˢ (n ∷ ns) < x ≔ u >
      ≡⟨⟩
    x ⇗ⁿ n [ x ≔ u ] ∷ x ⇗ˢ ns < x ≔ u >
      ≡⟨ cong₂ _∷_ (⇗ⁿ∘[≔]-id x u n) (⇗ˢ∘<≔>-id x u ns) ⟩
    n ∷ ns
    ∎
    where open ≡-Reasoning

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


  ↷/Nf/ {i = i} i↷j (x′ ·ⁿ ns) x h | l | [ ≡l ] | ⟳ˣ
    rewrite sym ≡l = begin
    ↷-cong i↷j /Nf/ (x′ ·ⁿ ns)
      ≡⟨ /Nf/∘·ⁿ (↷-cong i↷j) x′ ns ⟩
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ cong₂ _·ⁿ_ (sym $ helper) (↷/Sp/ i↷j ns x h) ⟩
    x ·ⁿ (i ⇗ˢ ns < i ⇗ˣ x′ ≔ x ·η [] >)
      ≡⟨ sym $ ◇∘·η x [] ((i ⇗ˢ ns) < i ⇗ˣ x′ ≔ x ·η [] >) ⟩
    (x ·η []) ◇ (i ⇗ˢ ns < i ⇗ˣ x′ ≔ x ·η [] >)
    ∎
    where
    open ≡-Reasoning
    p1 : x′ ≡ sym (↷-cong i↷j) /Var/ x
    p1 = ⇗ˣ-inj i x′ (sym (↷-cong i↷j) /Var/ x) (sym h)
    helper : x ≡ ↷-cong i↷j /Var/ x′
    helper = /Var/∘sym x′ x (↷-cong i↷j) p1
 
  ↷/Nf/ {i = i} i↷j (x′ ·ⁿ ns) x h | .(j ⇗ˣ v) | [ ≡l ] | j ↗ˣ v = begin
    ↷-cong i↷j /Nf/ (x′ ·ⁿ ns)
      ≡⟨ /Nf/∘·ⁿ (↷-cong i↷j) x′ ns ⟩
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ cong₂ _·ⁿ_ (↷/Var/ i↷j (i ⇗ˣ x′ ≡ j ⇗ˣ v ∋ ≡l)) (↷/Sp/ i↷j ns x h) ⟩
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
              ([≔]∘·η∘⇗ˣ vz n x (vz ⇗ˢ ns₁ ∷ʳ vz ·η [])) ⟩
    (x ·η ((vz ⇗ˢ ns₁ ∷ʳ vz ·η []) < vz ≔ n >)) ◇ ns₂
      ≡⟨ cong (λ ns → (x ·η ns) ◇ ns₂)
              (<≔>∘∷ʳ (vz ⇗ˢ ns₁) (vz ·η []) vz n) ⟩
    (x ·η (vz ⇗ˢ ns₁ < vz ≔ n > ∷ʳ (vz ·η []) [ vz ≔ n ])) ◇ ns₂
      ≡⟨ cong₂ (λ us u → (x ·η (us ∷ʳ u)) ◇ ns₂)
               (⇗ˢ∘<≔>-id vz n ns₁) ([≔]∘·η vz [] n) ⟩
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
              (<≔>∘∷ʳ∘⇗ˢ x u ns) ⟩
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

mutual

  -- /Nf/∘[≔]∘[≔]

  /Nf/∘[≔]∘[≔] : ∀ {τ Γ σ₁ σ₂}
    (x : Var Γ σ₁) (u₁ : Nf (Γ - x) σ₁)
    (y : Var (Γ - x) σ₂) (u₂ : Nf ((Γ - x) - y) σ₂)
    (n : Nf Γ τ) →
    -∘- x y /Nf/ ((n [ x ≔ u₁ ]) [ y ≔ u₂ ]) ≡
      (n [ x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
        [ x ⇘ˣ y ≔ -∘- x y /Nf/ (u₁ [ y ≔ u₂ ]) ]

  /Nf/∘[≔]∘[≔] {○} x u₁ y u₂ (v ·ⁿ ns) with varDiff x v

  /Nf/∘[≔]∘[≔] {○} x u₁ y u₂ (.x ·ⁿ ns) | ⟳ˣ = begin
    -∘- x y /Nf/ (u₁ ◇ (ns < x ≔ u₁ >)) [ y ≔ u₂ ]
      ≡⟨ helper ⟩
    (((x ⇗ˣ y) ⇗ˣ (x ⇘ˣ y) ·ⁿ ns)
      [ x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
      [ x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] ]
      ≡⟨ cong (λ x′ → ((x′ ·ⁿ ns) [ x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
                           [ x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] ])
           (⇗⇘ˣ-id x y) ⟩
    ((x ·ⁿ ns)
      [ x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
      [ x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] ]
    ∎
    where
    open ≡-Reasoning
    helper : -∘- x y /Nf/ (u₁ ◇ (ns < x ≔ u₁ >)) [ y ≔ u₂ ] ≡
             (((x ⇗ˣ y) ⇗ˣ (x ⇘ˣ y) ·ⁿ ns) [ x ⇗ˣ y ≔
                  (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
                   [ x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] ]
    helper rewrite varDiff-↗ˣ (x ⇗ˣ y) (x ⇘ˣ y) | varDiff-⟳ˣ (x ⇘ˣ y) = begin
      -∘- x y /Nf/ (u₁ ◇ (ns < x ≔ u₁ >)) [ y ≔ u₂ ]
        ≡⟨ cong (_/Nf/_ (-∘- x y)) ([≔]∘◇ y u₂ u₁ (ns < x ≔ u₁ >)) ⟩
      -∘- x y /Nf/ (u₁ [ y ≔ u₂ ]) ◇ ((ns < x ≔ u₁ >) < y ≔ u₂ >)
        ≡⟨ /Nf/∘◇ (-∘- x y) (u₁ [ y ≔ u₂ ]) ((ns < x ≔ u₁ >) < y ≔ u₂ >) ⟩
      (-∘- x y /Nf/ u₁ [ y ≔ u₂ ]) ◇
        (-∘- x y /Sp/ (ns < x ≔ u₁ >) < y ≔ u₂ >)
        ≡⟨ cong (_◇_ (-∘- x y /Nf/ u₁ [ y ≔ u₂ ]))
                (/Sp/∘<≔>∘<≔> x u₁ y u₂ ns) ⟩
      (-∘- x y /Nf/ u₁ [ y ≔ u₂ ]) ◇
        ((ns < x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) >)
          < x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] >)
      ∎

  /Nf/∘[≔]∘[≔] {○} x u₁ y u₂ (.(x ⇗ˣ v) ·ⁿ ns) | .x ↗ˣ v  with varDiff y v

  /Nf/∘[≔]∘[≔] {○} x u₁ .v u₂ (.(x ⇗ˣ v) ·ⁿ ns) | .x ↗ˣ v | ⟳ˣ
    rewrite varDiff-⟳ˣ (x ⇗ˣ v) = begin
    -∘- x v /Nf/ u₂ ◇ ((ns < x ≔ u₁ >) < v ≔ u₂ >)
      ≡⟨ /Nf/∘◇ (-∘- x v) u₂ ((ns < x ≔ u₁ >) < v ≔ u₂ >) ⟩
    (-∘- x v /Nf/ u₂) ◇ (-∘- x v /Sp/ (ns < x ≔ u₁ >) < v ≔ u₂ >)
      ≡⟨ cong₂ _◇_ refl (/Sp/∘<≔>∘<≔> x u₁ v u₂ ns) ⟩
    (-∘- x v /Nf/ u₂) ◇
      ((ns < x ⇗ˣ v ≔ (x ⇘ˣ v) ⇗ⁿ (-∘- x v /Nf/ u₂) >)
        < x ⇘ˣ v ≔ -∘- x v /Nf/ u₁ [ v ≔ u₂ ] >)
      ≡⟨ {!!} ⟩
    ((x ⇘ˣ v) ⇗ⁿ (-∘- x v /Nf/ u₂) ◇
      (ns < x ⇗ˣ v ≔ (x ⇘ˣ v) ⇗ⁿ (-∘- x v /Nf/ u₂) >))
        [ x ⇘ˣ v ≔ -∘- x v /Nf/ u₁ [ v ≔ u₂ ] ]
    ∎
    where
    open ≡-Reasoning
        

  /Nf/∘[≔]∘[≔] {○} x u₁ y u₂ (.(x ⇗ˣ (y ⇗ˣ v)) ·ⁿ ns)
    | .x ↗ˣ .(y ⇗ˣ v) | .y ↗ˣ v
    rewrite ⇗ˣ∘⇗ˣ x y v
          | varDiff-↗ˣ (x ⇗ˣ y) ((x ⇘ˣ y) ⇗ˣ (-∘- x y /Var/ v))
          | varDiff-↗ˣ (x ⇘ˣ y) (-∘- x y /Var/ v) = begin
    -∘- x y /Nf/ v ·ⁿ ((ns < x ≔ u₁ >) < y ≔ u₂ >)
      ≡⟨ /Nf/∘·ⁿ (-∘- x y) v ((ns < x ≔ u₁ >) < y ≔ u₂ >) ⟩
    (-∘- x y /Var/ v) ·ⁿ (-∘- x y /Sp/ (ns < x ≔ u₁ >) < y ≔ u₂ >)
      ≡⟨ cong (_·ⁿ_ (-∘- x y /Var/ v)) (/Sp/∘<≔>∘<≔> x u₁ y u₂ ns) ⟩
    (-∘- x y /Var/ v) ·ⁿ
      ((ns < x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) >) < x ⇘ˣ y ≔
        -∘- x y /Nf/ u₁ [ y ≔ u₂ ] >)
    ∎
    where open ≡-Reasoning

  /Nf/∘[≔]∘[≔] {τ₁ ⇒ τ₂} x u₁ y u₂ (ƛⁿ n) = begin
    -∘- x y /Nf/ (ƛⁿ n [ x ≔ u₁ ]) [ y ≔ u₂ ]
      ≡⟨⟩
    -∘- x y /Nf/ ƛⁿ ((n [ vs x ≔ vz ⇗ⁿ u₁ ]) [ vs y ≔ vz ⇗ⁿ u₂ ])
      ≡⟨ /Nf/∘ƛⁿ (-∘- x y) ((n [ vs x ≔ vz ⇗ⁿ u₁ ]) [ vs y ≔ vz ⇗ⁿ u₂ ]) ⟩
    ƛⁿ (-∘- x y <,< τ₁ /Nf/ (n [ vs x ≔ vz ⇗ⁿ u₁ ]) [ vs y ≔ vz ⇗ⁿ u₂ ])
      ≡⟨ cong ƛⁿ (/Nf/∘[≔]∘[≔] (vs x) (vz ⇗ⁿ u₁) (vs y) (vz ⇗ⁿ u₂) n) ⟩
    ƛⁿ ((n [ vs (x ⇗ˣ y) ≔ vs (x ⇘ˣ y) ⇗ⁿ (-∘- x y <,< τ₁ /Nf/ vz ⇗ⁿ u₂)])
           [ vs (x ⇘ˣ y) ≔ (-∘- x y) <,< τ₁ /Nf/ (vz ⇗ⁿ u₁)
             [ vs y ≔ vz ⇗ⁿ u₂ ] ])
      ≡⟨ cong₂ (λ n₁ n₂ →
           ƛⁿ ((n [ vs (x ⇗ˣ y) ≔ n₁ ]) [ vs (x ⇘ˣ y) ≔ n₂ ]))
           helper₁ helper₂ ⟩
    ƛⁿ ((n [ vs (x ⇗ˣ y) ≔ vz ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂)) ])
           [ vs (x ⇘ˣ y) ≔ vz ⇗ⁿ (-∘- x y /Nf/ u₁ [ y ≔ u₂ ]) ])
      ≡⟨⟩
      (ƛⁿ n [ x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
            [ x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] ]
    ∎
    where
    open ≡-Reasoning
    helper₁ = begin
      vs (x ⇘ˣ y) ⇗ⁿ (-∘- x y <,< τ₁ /Nf/ vz ⇗ⁿ u₂)
        ≡⟨ cong (_⇗ⁿ_ (vs (x ⇘ˣ y))) (/Nf/∘<,< (-∘- x y) u₂) ⟩
      vs (x ⇘ˣ y) ⇗ⁿ (vz ⇗ⁿ (-∘- x y /Nf/ u₂))
        ≡⟨ sym $ ⇗ⁿ∘⇗ⁿ vz (x ⇘ˣ y) (-∘- x y /Nf/ u₂) ⟩
      vz ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂))
      ∎
    helper₂ = begin
      -∘- x y <,< τ₁ /Nf/ vz ⇗ⁿ u₁ [ vs y ≔ vz ⇗ⁿ u₂ ]
        ≡⟨ cong (_/Nf/_ (-∘- x y <,< τ₁)) (sym $ /Nf/∘[≔] vz y u₂ u₁) ⟩
      -∘- x y <,< τ₁ /Nf/ vz ⇗ⁿ (u₁ [ y ≔ u₂ ])
        ≡⟨ /Nf/∘<,< (-∘- x y) (u₁ [ y ≔ u₂ ]) ⟩
      vz ⇗ⁿ (-∘- x y /Nf/ u₁ [ y ≔ u₂ ])
      ∎

  -- /Sp/∘<≔>∘<≔>

  /Sp/∘<≔>∘<≔> : ∀ {Γ σ₁ σ₂ τ}
    (x : Var Γ σ₁) (u₁ : Nf (Γ - x) σ₁)
    (y : Var (Γ - x) σ₂) (u₂ : Nf ((Γ - x) - y) σ₂)
    (ns : Sp Γ τ ○) →
    -∘- x y /Sp/ ((ns < x ≔ u₁ >) < y ≔ u₂ >) ≡
        (ns < x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) >)
          < x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] >

  /Sp/∘<≔>∘<≔> x u₁ y u₂ [] =
    /Sp/∘[] (-∘- x y)

  /Sp/∘<≔>∘<≔> x u₁ y u₂ (n ∷ ns) = begin
    -∘- x y /Sp/ ((n ∷ ns) < x ≔ u₁ >) < y ≔ u₂ >
      ≡⟨⟩
    -∘- x y /Sp/ ((n [ x ≔ u₁ ]) [ y ≔ u₂ ] ∷ (ns < x ≔ u₁ >) < y ≔ u₂ >)
      ≡⟨ /Sp/∘∷ (-∘- x y) ((n [ x ≔ u₁ ]) [ y ≔ u₂ ])
                          ((ns < x ≔ u₁ >) < y ≔ u₂ >) ⟩
    (-∘- x y /Nf/ (n [ x ≔ u₁ ]) [ y ≔ u₂ ]) ∷
      (-∘- x y /Sp/ (ns < x ≔ u₁ >) < y ≔ u₂ >)
      ≡⟨ cong₂ _∷_
               (/Nf/∘[≔]∘[≔] x u₁ y u₂ n)
               (/Sp/∘<≔>∘<≔> x u₁ y u₂ ns) ⟩
    (n [ x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) ])
      [ x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] ]
        ∷
    (ns < x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) >)
      < x ⇘ˣ y ≔ -∘- x y /Nf/ u₁ [ y ≔ u₂ ] >
    ≡⟨⟩
      ((n ∷ ns) < x ⇗ˣ y ≔ (x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ u₂) >) < x ⇘ˣ y ≔
      -∘- x y /Nf/ u₁ [ y ≔ u₂ ] >
    ∎
    where open ≡-Reasoning


  -- [≔]∘·β

  [≔]∘·β : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ) (u : Nf (Γ - x) σ)
    (n₁ : Nf Γ (τ₂ ⇒ τ₁)) (n₂ : Nf Γ τ₂) →
    (n₁ ·β n₂) [ x ≔ u ] ≡ (n₁ [ x ≔ u ]) ·β  (n₂ [ x ≔ u ])

  [≔]∘·β x u (ƛⁿ t₁) t₂ =
    /Nf/∘[≔]∘[≔] vz t₂ x u t₁

  -- [≔]∘◇

  [≔]∘◇ : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ) (u : Nf (Γ - x) σ)
    (n : Nf Γ τ₁) (ns : Sp Γ τ₁ τ₂) →
    (n ◇ ns) [ x ≔ u ] ≡ (n [ x ≔ u ]) ◇ (ns < x ≔ u >)

  [≔]∘◇ x u n [] = refl

  [≔]∘◇ x u n (n₁ ∷ ns) = begin
    (n ◇ (n₁ ∷ ns)) [ x ≔ u ]
      ≡⟨⟩
    ((n ·β n₁) ◇ ns) [ x ≔ u ]
      ≡⟨ [≔]∘◇ x u (n ·β n₁) ns ⟩
    ((n ·β n₁) [ x ≔ u ]) ◇ (ns < x ≔ u >)
      ≡⟨ cong (flip _◇_ (ns < x ≔ u >)) ([≔]∘·β x u n n₁) ⟩
    ((n [ x ≔ u ]) ·β (n₁ [ x ≔ u ])) ◇ (ns < x ≔ u >)
      ≡⟨⟩
    (n [ x ≔ u ]) ◇ ((n₁ ∷ ns) < x ≔ u >)
    ∎
    where open ≡-Reasoning


-- Normalization and substitution commute.

nf∘substTm : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) (u : Tm (Γ - x) σ) →
  nf (substTm t x u) ≡ (nf t) [ x ≔ nf u ]

nf∘substTm (var v) x u with varDiff x v

nf∘substTm (var v) .v u | ⟳ˣ =
  sym $ [≔]∘·η v [] (nf u)

nf∘substTm (var .(x ⇗ˣ v)) x u | .x ↗ˣ v =
  sym $ [≔]∘·η∘⇗ˣ x (nf u) v []

nf∘substTm (ƛ t) x u = begin
  nf (substTm (ƛ t) x u)
    ≡⟨⟩
  ƛⁿ (nf (substTm t (vs x) (vz ⇗ u)))
    ≡⟨ cong ƛⁿ (nf∘substTm t (vs x) (vz ⇗ u)) ⟩
  ƛⁿ (nf t [ vs x ≔ nf (vz ⇗ u) ])
    ≡⟨ cong (λ n′ → ƛⁿ (nf t [ vs x ≔ n′ ])) (nf∘⇗ vz u) ⟩
  ƛⁿ (nf t [ vs x ≔ vz ⇗ⁿ nf u ])
    ≡⟨⟩
  nf (ƛ t) [ x ≔ nf u ]
  ∎
  where open ≡-Reasoning

nf∘substTm (t₁ · t₂) x u = begin
  nf (substTm (t₁ · t₂) x u)
    ≡⟨⟩
  nf (substTm t₁ x u) ·β nf (substTm t₂ x u)
    ≡⟨ cong₂ _·β_ (nf∘substTm t₁ x u) (nf∘substTm t₂ x u) ⟩
  (nf t₁ [ x ≔ nf u ]) ·β (nf t₂ [ x ≔ nf u ])
    ≡⟨ sym $ [≔]∘·β x (nf u) (nf t₁) (nf t₂) ⟩
  (nf t₁ ·β nf t₂) [ x ≔ nf u ]
    ≡⟨⟩
  nf (t₁ · t₂) [ x ≔ nf u ]
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
    ≡⟨ sym $ nf∘substTm t vz u ⟩
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

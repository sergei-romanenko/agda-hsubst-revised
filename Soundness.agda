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

  ⇗ˢ∘⇗ˢ x y ε = begin
    x ⇗ˢ (y ⇗ˢ ε)
      ≡⟨⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ε)
      ≡⟨ cong (λ ns → (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ns))
              (sym $ /Sp/∘ε (-∘- x y)) ⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ ε))
    ∎
    where open ≡-Reasoning

  ⇗ˢ∘⇗ˢ x y (n , ns) = begin
    x ⇗ˢ (y ⇗ˢ (n , ns))
      ≡⟨⟩
    (x ⇗ⁿ (y ⇗ⁿ n)) , (x ⇗ˢ (y ⇗ˢ ns))
      ≡⟨ cong₂ _,_ (⇗ⁿ∘⇗ⁿ x y n) (⇗ˢ∘⇗ˢ x y ns) ⟩
    ((x ⇗ˣ y) ⇗ⁿ ((x ⇘ˣ y) ⇗ⁿ (-∘- x y /Nf/ n))) ,
        ((x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ ns)))
      ≡⟨⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ((-∘- x y /Nf/ n) , (-∘- x y /Sp/ ns)))
      ≡⟨ cong (λ ns₁ → (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ ns₁))
              (sym $ /Sp/∘, (-∘- x y) n ns) ⟩
    (x ⇗ˣ y) ⇗ˢ ((x ⇘ˣ y) ⇗ˢ (-∘- x y /Sp/ (n , ns)))
    ∎
    where open ≡-Reasoning


mutual

  ⇗ˢ∘,: : ∀ {Γ σ₁ σ₂ τ₁ τ₂} (x : Var Γ σ₁) (ns : Sp (Γ - x) σ₂ (τ₁ ⇒ τ₂)) →
    vs x ⇗ˢ ((vz ⇗ˢ ns) ,: (vz ·η ε)) ≡
      (vz ⇗ˢ (x ⇗ˢ ns)) ,: (vz ·η ε)

  ⇗ˢ∘,: x ε = cong (λ n → n , ε) (⇗ⁿ∘·η (vs x) vz ε)
  ⇗ˢ∘,: x (n , ns) = begin
    vs x ⇗ˢ ((vz ⇗ˢ (n , ns)) ,: (vz ·η ε))
      ≡⟨⟩
    (vs x ⇗ⁿ (vz ⇗ⁿ n)) , (vs x ⇗ˢ ((vz ⇗ˢ ns) ,: (vz ·η ε)))
      ≡⟨ cong₂ _,_ (sym $ ⇗ⁿ∘⇗ⁿ vz x n) (⇗ˢ∘,: x ns) ⟩
    (vz ⇗ⁿ (x ⇗ⁿ n))    , ((vz ⇗ˢ (x ⇗ˢ ns)) ,: (vz ·η ε))
      ≡⟨⟩
    (vz ⇗ˢ (x ⇗ˢ (n , ns))) ,: (vz ·η ε)
    ∎
    where open ≡-Reasoning


  ⇗ⁿ∘·η : ∀ {τ Γ σ₁ σ₂} (x : Var Γ σ₁)
            (y : Var (Γ - x) σ₂) (ns : Sp (Γ - x) σ₂ τ) →
    x ⇗ⁿ (y ·η ns) ≡ (x ⇗ˣ y) ·η (x ⇗ˢ ns)

  ⇗ⁿ∘·η {○} x y ns = refl
  ⇗ⁿ∘·η {τ₁ ⇒ τ₂} x y ns = begin
    x ⇗ⁿ (y ·η ns)
      ≡⟨⟩
    ƛⁿ (vs x ⇗ⁿ (vs y ·η ((vz ⇗ˢ ns) ,: (vz ·η ε))))
      ≡⟨ cong ƛⁿ (⇗ⁿ∘·η (vs x) (vs y) ((vz ⇗ˢ ns) ,: (vz ·η ε))) ⟩
    ƛⁿ (vs (x ⇗ˣ y) ·η (vs x ⇗ˢ ((vz ⇗ˢ ns) ,: (vz ·η ε))))
      ≡⟨ cong (λ u → ƛⁿ (vs (x ⇗ˣ y) ·η u))
              (⇗ˢ∘,: x ns) ⟩
    ƛⁿ (vs (x ⇗ˣ y) ·η ((vz ⇗ˢ (x ⇗ˢ ns)) ,: (vz ·η ε)))
      ≡⟨⟩
    (x ⇗ˣ y) ·η (x ⇗ˢ ns)
    ∎
    where open ≡-Reasoning

postulate

  ⇗ⁿ∘·β : ∀ {Γ σ τ₁ τ₂} (x : Var Γ σ)
            (n₁ : Nf (Γ - x) (τ₁ ⇒ τ₂)) (n₂ : Nf (Γ - x) τ₁) →
    x ⇗ⁿ (n₁ ·β n₂) ≡ (x ⇗ⁿ n₁) ·β (x ⇗ⁿ n₂)

--⇗ⁿ∘·β x (ƛⁿ n₁) n₂ = {!!}

-- nf∘⇗

nf∘⇗ : ∀ {Γ σ τ} (x : Var Γ σ) (t : Tm (Γ - x) τ) →
  nf (x ⇗ t) ≡ x ⇗ⁿ (nf t)

nf∘⇗ x (var x′) =
  sym $ ⇗ⁿ∘·η x x′ ε
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


-- _+Sp+_

_+Sp+_ : ∀ {Γ σ₁ σ₂ σ₃} (ns₁ : Sp Γ σ₁ σ₂) (ns₂ : Sp Γ σ₂ σ₃) → Sp Γ σ₁ σ₃

ε +Sp+ ns₂ = ns₂
(n , ns₁) +Sp+ ns₂ = n , (ns₁ +Sp+ ns₂)

-- +Sp+ε

+Sp+ε : ∀ {Γ σ τ} (ns : Sp Γ σ τ) → ns +Sp+ ε ≡ ns

+Sp+ε ε = refl
+Sp+ε (n , ns) = cong (λ u → n , u) (+Sp+ε ns)

-- +Sp+∘,

+Sp+∘, : ∀ {Γ σ₁ σ₂ σ₃ τ}
           (ns₁ : Sp Γ σ₁ (τ ⇒ σ₂)) (n : Nf Γ τ) (ns₂ : Sp Γ σ₂ σ₃) →
  ns₁ +Sp+ (n , ns₂) ≡ (ns₁ ,: n) +Sp+ ns₂

+Sp+∘, ε n ns₂ = refl
+Sp+∘, (n′ , ns₁) n ns₂ = cong (λ u → n′ , u) (+Sp+∘, ns₁ n ns₂)


mutual

  ↷/Var/·ⁿ/Sp/ : ∀ {Γ σ τ} {i j : Var Γ σ}  (i↷j : i ↷ j)
                 (x′ : Var (Γ - i) τ) (ns : Sp (Γ - i) τ ○) (x : Var (Γ - j) σ)
                 (l : Var Γ τ) → l ≡ i ⇗ˣ x′ →
                 i ⇗ˣ ((sym $ ↷-cong i↷j) /Var/ x) ≡ j →
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns) ≡
      (l ·ⁿ (i ⇗ˢ ns)) [ j ≔ (x ·η ε) ]

  ↷/Var/·ⁿ/Sp/ {Γ} {σ} {τ} {i} {j} i↷j x′ ns x l l≡ h with varDiff j l

  ↷/Var/·ⁿ/Sp/ {i = i} i↷j x′ ns x l l≡ h | ⟳ˣ = {!!}
{-
    begin
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ {! !} ⟩
    (x ·η ε) ◇ ((i ⇗ˢ ns) < l ≔ x ·η ε >)
    ∎
    where open ≡-Reasoning
-}

  ↷/Var/·ⁿ/Sp/ {i = i} i↷j x′ ns x .(j ⇗ˣ v) l≡ h | j ↗ˣ v = {!!}
{-
  begin
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ {!!} ⟩
    v ·ⁿ ((i ⇗ˢ ns) < j ≔ x ·η ε >)
    ∎
    where open ≡-Reasoning
-}

  ↷/Nf/ : ∀ {Γ σ τ} {i j : Var Γ σ} (i↷j : i ↷ j)
              (n : Nf (Γ - i) τ) (x : Var (Γ - j) σ) →
              i ⇗ˣ ((sym $ ↷-cong i↷j) /Var/ x) ≡ j →
    (↷-cong i↷j) /Nf/ n ≡ (i ⇗ⁿ n) [ j ≔ (x ·η ε) ]

  ↷/Nf/ {i = i} {j = j} i↷j (ƛⁿ {σ = σ} n) x h = begin
    ↷-cong i↷j /Nf/ ƛⁿ n
      ≡⟨ /Nf/∘ƛⁿ (↷-cong i↷j) n ⟩
    ƛⁿ ((↷-cong i↷j <,< σ) /Nf/ n)
      ≡⟨⟩
    ƛⁿ ((↷-cong (↷-s i↷j)) /Nf/ n)
      ≡⟨ cong ƛⁿ (↷/Nf/ (↷-s i↷j) n (vs x) helper) ⟩
    ƛⁿ ((vs i ⇗ⁿ n) [ vs j ≔ vs x ·η ε ])
      ≡⟨ cong (λ u → ƛⁿ ((vs i ⇗ⁿ n) [ vs j ≔ u ])) (sym $ ⇗ⁿ∘·η vz x ε) ⟩
    ƛⁿ ((vs i ⇗ⁿ n) [ vs j ≔ vz ⇗ⁿ (x ·η ε) ])
      ≡⟨⟩
    (i ⇗ⁿ ƛⁿ n) [ j ≔ x ·η ε ]
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

  ↷/Nf/ {i = i} {j = j} i↷j (x′ ·ⁿ ns) x h = begin
    ↷-cong i↷j /Nf/ (x′ ·ⁿ ns)
      ≡⟨ /Nf/∘·ⁿ (↷-cong i↷j) x′ ns ⟩
    (↷-cong i↷j /Var/ x′) ·ⁿ (↷-cong i↷j /Sp/ ns)
      ≡⟨ ↷/Var/·ⁿ/Sp/ i↷j x′ ns x (i ⇗ˣ x′) refl h ⟩
    (i ⇗ⁿ (x′ ·ⁿ ns)) [ j ≔ x ·η ε ]
    ∎
    where open ≡-Reasoning

  ↷/Sp/ : ∀ {Γ σ τ ρ} {i j : Var Γ σ} (i↷j : i ↷ j)
            (ns : Sp (Γ - i) ρ τ) (x : Var (Γ - j) σ) →
            i ⇗ˣ ((sym $ ↷-cong i↷j) /Var/ x) ≡ j →
    ↷-cong i↷j /Sp/ ns ≡ (i ⇗ˢ ns) < j ≔ (x ·η ε) >

  ↷/Sp/ i↷j ε x h =
    /Sp/∘ε (↷-cong i↷j)

  ↷/Sp/ {i = i} {j = j} i↷j (n , ns) x h = begin
    ↷-cong i↷j /Sp/ (n , ns)
      ≡⟨ /Sp/∘, (↷-cong i↷j) n ns ⟩
    (↷-cong i↷j /Nf/ n) , (↷-cong i↷j /Sp/ ns)
      ≡⟨ cong₂ _,_ (↷/Nf/ i↷j n x h) (↷/Sp/ i↷j ns x h) ⟩
    ((i ⇗ⁿ n) [ j ≔ x ·η ε ]) , ((i ⇗ˢ ns) < j ≔ x ·η ε >)
      ≡⟨⟩
    (i ⇗ˢ (n , ns)) < j ≔ x ·η ε >
    ∎
    where open ≡-Reasoning


  -- ◇∘·η

  ◇∘·η : ∀ {Γ σ τ} (x : Var Γ σ) (ns₁ : Sp Γ σ τ) (ns₂ : Sp Γ τ ○) →
      (x ·η ns₁) ◇ ns₂ ≡ x ·ⁿ (ns₁ +Sp+ ns₂)

  ◇∘·η x ns₁ ε = begin
    (x ·η ns₁) ◇ ε
      ≡⟨⟩
    x ·ⁿ ns₁
      ≡⟨ cong (_·ⁿ_ x) (sym $ +Sp+ε ns₁) ⟩
    x ·ⁿ (ns₁ +Sp+ ε)
    ∎
    where open ≡-Reasoning

  ◇∘·η x ns₁ (n , ns₂) = begin
    (x ·η ns₁) ◇ (n , ns₂)
      ≡⟨⟩
    ((vs x ·η ((vz ⇗ˢ ns₁) ,: (vz ·η ε))) [ vz ≔ n ]) ◇ ns₂
      ≡⟨ {!!} ⟩
    (x ·η (((vz ⇗ˢ ns₁) < vz ≔ n >) ,: ((vz ·η ε) [ vz ≔ n ]))) ◇ ns₂
      ≡⟨ cong₂ (λ us u → (x ·η (us ,: u)) ◇ ns₂)
               {!!}
               ([≔]∘·η vz ε n) ⟩
    (x ·η (ns₁ ,: n)) ◇ ns₂
      ≡⟨ ◇∘·η x (ns₁ ,: n) ns₂ ⟩
    x ·ⁿ ((ns₁ ,: n) +Sp+ ns₂)
      ≡⟨ cong (_·ⁿ_ x) (sym $ +Sp+∘, ns₁ n ns₂) ⟩
    x ·ⁿ (ns₁ +Sp+ (n , ns₂))
    ∎
    where open ≡-Reasoning

  [≔]∘·η : ∀ {τ Γ σ} (x : Var Γ σ) (ns : Sp Γ σ τ) (u : Nf (Γ - x) σ) →
    (x ·η ns) [ x ≔ u ] ≡ u ◇ (ns < x ≔ u >)

  [≔]∘·η = {!!}

-- ƛⁿ∘·β

ƛⁿ∘·β : ∀ {Γ σ τ} (n : Nf Γ (σ ⇒ τ))  →
  ƛⁿ ((vz ⇗ⁿ n) ·β (vz ·η ε)) ≡ n

ƛⁿ∘·β {Γ} {σ} {τ} (ƛⁿ n) = begin
  ƛⁿ ((vz ⇗ⁿ ƛⁿ n) ·β (vz ·η ε))
    ≡⟨⟩
  ƛⁿ ((vs vz ⇗ⁿ n) [ vz ≔ vz ·η ε ])
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
  ƛⁿ (nf (vz ⇗ t) ·β (vz ·η ε))
    ≡⟨ cong (λ n → ƛⁿ (n ·β (vz ·η ε))) (nf∘⇗ vz t) ⟩
  ƛⁿ ((vz ⇗ⁿ nf t) ·β (vz ·η ε))
    ≡⟨ ƛⁿ∘·β (nf t) ⟩
  nf t
  ∎
  where open ≡-Reasoning

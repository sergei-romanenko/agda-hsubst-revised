--
-- Terms are convertible to their normal forms
--     ⌈ nf t ⌉ ≈βη t
--

module Completeness where

--open import Data.Star
--open import Data.Star.Properties

open import Data.Empty

open import Function

open import Relation.Binary.PropositionalEquality as P

open import Stlc
open import Normalization
open import BetaEta

_⇘ˣ_ : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ) → Var (Γ - (x ⇗ˣ y)) σ

vz   ⇘ˣ y    = vz
vs x ⇘ˣ vz   = x
vs x ⇘ˣ vs y = vs (x ⇘ˣ y)

con-- : ∀ {Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ) →
              (Γ - x) - y ≡ (Γ - (x ⇗ˣ y)) - (x ⇘ˣ y)

con-- vz     y      = refl
con-- (vs x) vz     =
  refl
con-- (vs {τ = τ} x) (vs y) =
  cong (flip _,_ τ) (con-- x y)

-- ⇗∘substTm

{-
--⇗∘substTm : ∀ {Γ σ τ} (x : Var Γ σ) (u : Tm (Γ - x) σ)
--              (t : Tm ((Γ - x) , σ) τ) →
⇗∘substTm : ∀ {Γ σ τ} (x : Var Γ σ) (u : Tm (Γ - x) σ)
              (t : Tm {!!} τ) →
  x ⇗ substTm t vz u ≈βη substTm (vs x ⇗ t) vz (x ⇗ u)

⇗∘substTm = {!!}
-}
{-
substTm∘⇗ : ∀ {Γ σ σ′ τ} (x : Var Γ σ) (u : Tm (Γ - x) σ′)
                   (t : Tm ((Γ - x) , σ′) τ)  →
           substTm (vs x ⇗ t) vz (x ⇗ u) ≈βη x ⇗ substTm t vz u

substTm∘⇗ x u t = {!!}
-}

-- var∘subst

var∘subst : ∀ {Γ₁ Γ₂ τ} (p : Γ₁ ≡ Γ₂) (z : Var Γ₁ τ) →
                var (subst (flip Var τ) p z) ≡ subst (flip Tm τ) p (var z)
var∘subst refl z = refl

-- ⇗ˣ∘⇗ˣ

⇗ˣ∘⇗ˣ : ∀ {ρ Γ σ τ} (x : Var Γ σ) (y : Var (Γ - x) τ)
          (v : Var ((Γ - x) - y) ρ) →
        x ⇗ˣ (y ⇗ˣ v) ≡
          (x ⇗ˣ y) ⇗ˣ ((x ⇘ˣ y) ⇗ˣ (subst (flip Var ρ) (con-- x y) v))

⇗ˣ∘⇗ˣ = {!!}

-- ⇗∘⇗

⇗∘⇗ : ∀ {Γ σ₁ σ₂ τ} (x : Var Γ σ₁) (y : Var (Γ - x) σ₂)
           (t : Tm ((Γ - x) - y) τ) →
    x ⇗ (y ⇗ t) ≡
      (x ⇗ˣ y) ⇗ ((x ⇘ˣ  y) ⇗ (subst (flip Tm τ) (con-- x y) t))

⇗∘⇗ x y (var {σ = σ} x₁) = begin
  x ⇗ (y ⇗ var x₁)
    ≡⟨ refl ⟩
  var (x ⇗ˣ (y ⇗ˣ x₁))
    ≡⟨ ? ⟩
  ?
    ≡⟨ ⇗∘⇗ x y (var x₁) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ subst (flip Tm σ) (con-- x y) (var x₁))
{-
  x ⇗ (y ⇗ var x₁)
    ≡⟨ refl ⟩
  var (x ⇗ˣ (y ⇗ˣ x₁))
    ≡⟨ cong var (⇗ˣ∘⇗ˣ x y x₁) ⟩
  var ((x ⇗ˣ y) ⇗ˣ ((x ⇘ˣ y) ⇗ˣ subst (flip Var σ) (con-- x y) x₁))
    ≡⟨ refl ⟩
  (x ⇗ˣ y) ⇗ var ((x ⇘ˣ y) ⇗ˣ subst (flip Var σ) (con-- x y) x₁)
    ≡⟨ refl ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ var (subst (flip Var σ) (con-- x y) x₁))
    ≡⟨ cong (λ t → (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ t))
            (var∘subst (con-- x y) x₁) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ subst (flip Tm σ) (con-- x y) (var x₁))
-}
  ∎
  where open ≡-Reasoning

⇗∘⇗ x y (ƛ {σ = σ} {τ = τ} t) = begin
  x ⇗ (y ⇗ ƛ t)
    ≡⟨ refl ⟩
  ƛ (vs x ⇗ (vs y ⇗ t))
    ≡⟨ ⇗∘⇗ x y (ƛ t) ⟩
  (x ⇗ˣ y) ⇗ ((x ⇘ˣ y) ⇗ subst (flip Tm (σ ⇒ τ)) (con-- x y) (ƛ t))
  ∎
  where open ≡-Reasoning

⇗∘⇗ x y (t₁ · t₂) = {!!}


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
    ≈⟨ {!!} ⟩
  x ⇗ substTm t vz u
  ∎
  where
  open βη-Reasoning
{-
  helper : ∀ {Γ σ σ′ τ} (x : Var Γ σ) (u : Tm (Γ - x) σ′)
                     (t : Tm ((Γ - x) , σ′) τ)  →
    substTm (vs x ⇗ t) vz (x ⇗ u) ≈βη x ⇗ substTm t vz u
  helper = {!!}
-}
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


-- substVar∘⟳ˣ

substVar∘⟳ˣ : ∀ {Γ σ} (x : Var Γ σ) (u : Tm (Γ - x) σ) →
  varDiff x x ≡ ⟳ˣ x → substVar x x u ≈βη u

substVar∘⟳ˣ x u h rewrite h =
  βη-refl

-- substVar∘⇗ˣ

substVar∘⇗ˣ : ∀ {Γ σ τ} (x : Var Γ σ) (u : Tm (Γ - x) σ) (v : Var (Γ - x) τ) →
  varDiff x (x ⇗ˣ v) ≡ x ↗ˣ v → substVar (x ⇗ˣ v) x u ≡ var v

substVar∘⇗ˣ x u v h rewrite h = refl

-- substTm-cong

substTm-cong : ∀ {Γ σ τ} (t : Tm Γ τ) (x : Var Γ σ) {u₁ u₂ : Tm (Γ - x) σ} →
  u₁ ≈βη u₂ → substTm t x u₁ ≈βη substTm t x u₂

substTm-cong (var x′) x h with varDiff x x′
substTm-cong (var .x) x h | ⟳ˣ .x =
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

  ⌈⌉∘⇗ⁿ x (ƛ n) = begin
    ⌈ x ⇗ⁿ ƛ n ⌉
      ≡⟨ refl ⟩
    ƛ ⌈ vs x ⇗ⁿ n ⌉
      ≈⟨ ƛ-cong (⌈⌉∘⇗ⁿ (vs x) n) ⟩
    ƛ (vs x ⇗ ⌈ n ⌉)
      ≡⟨ refl ⟩
    x ⇗ ⌈ ƛ n ⌉
    ∎
    where open βη-Reasoning

  ⌈⌉∘⇗ⁿ x (x′ · ns) = begin
    ⌈ x ⇗ⁿ (x′ · ns) ⌉
      ≡⟨ refl ⟩
    var (x ⇗ˣ x′) ·⌈ x ⇗ˢ ns ⌉
      ≈⟨ ·⌈⌉∘⇗ⁿ x (var x′) ns ⟩
    x ⇗ (var x′ ·⌈ ns ⌉)
      ≡⟨ refl ⟩
    x ⇗ ⌈ x′ · ns ⌉
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

  ⌈⌉∘[≔] (ƛ n) x u = begin
    ⌈ ƛ n [ x ≔ u ] ⌉
      ≡⟨ refl ⟩
    ƛ ⌈ n [ vs x ≔ vz ⇗ⁿ u ] ⌉
      ≈⟨ ƛ-cong (⌈⌉∘[≔] n (vs x) (vz ⇗ⁿ u)) ⟩
    ƛ (substTm ⌈ n ⌉ (vs x) ⌈ vz ⇗ⁿ u ⌉)
      ≈⟨ ƛ-cong (substTm-cong ⌈ n ⌉ (vs x) (⌈⌉∘⇗ⁿ vz u)) ⟩
    ƛ (substTm ⌈ n ⌉ (vs x) (vz ⇗ ⌈ u ⌉))
      ≡⟨ refl ⟩
    substTm ⌈ ƛ n ⌉ x ⌈ u ⌉
    ∎
    where open βη-Reasoning

  ⌈⌉∘[≔] (x′ · ns) x u with varDiff x x′ | inspect (varDiff x) x′
  ⌈⌉∘[≔] (.x · ns) x u | ⟳ˣ .x | [ x≡ ] = begin
    ⌈ u ◇ (ns < x ≔ u >) ⌉
      ≈⟨ ⌈⌉∘◇ u (ns < x ≔ u >) ⟩
    ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉
      ≈⟨ ·⌈⌉-cong (ns < x ≔ u >) (βη-sym $ substVar∘⟳ˣ x ⌈ u ⌉ x≡) ⟩
    substVar x x ⌈ u ⌉ ·⌈ ns < x ≔ u > ⌉
      ≈⟨ ⌈⌉∘<≔> (var x) ns x u ⟩
    substTm (var x ·⌈ ns ⌉) x ⌈ u ⌉
    ∎
    where open βη-Reasoning


  ⌈⌉∘[≔] (.(x ⇗ˣ v) · ns) x u | .x ↗ˣ v | [ x≡ ] = begin
    var v ·⌈ ns < x ≔ u > ⌉
      ≡⟨ cong (λ z → z ·⌈ ns < x ≔ u > ⌉)
              (sym $ substVar∘⇗ˣ x ⌈ u ⌉ v x≡) ⟩
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

  ⌈⌉∘·β (ƛ n₁) n₂ = begin
    ⌈ ƛ n₁ ·β n₂ ⌉
      ≡⟨ refl ⟩
    ⌈ n₁ [ vz ≔ n₂ ] ⌉
      ≈⟨ ⌈⌉∘[≔] n₁ vz n₂ ⟩
    substTm ⌈ n₁ ⌉ vz ⌈ n₂ ⌉
      ≈⟨ βη-sym ≈-β ⟩
    ƛ ⌈ n₁ ⌉ · ⌈ n₂ ⌉
      ≡⟨ refl ⟩
    ⌈ ƛ n₁ ⌉ · ⌈ n₂ ⌉
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
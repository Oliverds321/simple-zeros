/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WindowD.lean — the window layer at a FREE buffer D (the "ParamsQ" D₀-generalisation).

The record fixes D₀ := √T ([eq:D0], Defs.lean) and phrases the I′-window objects
(Iprime, ZIprime, NIprime, NonIprime, S1/S2/offLine, s1/s2/p) and the window bookkeeping
(Assembly.lean §F0) at that value. The q-aspect paper needs the same layer at a free
buffer D (its design of record balances D₀; √T breaks the theorem's rate class — see the
companion notes). This file provides:

  * the D-generic mirrors of the window definitions (suffix `D`), with `rfl` bridges
    showing each specialises to the record's object at D = D0 T = √T;
  * the D-generic mirrors of the §F0 bookkeeping (`NIprimeD_eq`, `s1D_add_s2D_eq`,
    `s1D_add_s2D_le`, `s1D_le`, `card_ZIprimeD_le`), with `0 ≤ D` as a hypothesis in
    place of `Real.sqrt_nonneg`;
  * `Assembly.count_certificate_free`: the §6 moment certificate with the N(I′∖I) term
    abstracted to a function `NIIf` — the record's `count_certificate` never consumes
    the DEFINITION of `NII`, only its o(N) hypothesis, so the proof is verbatim.

Every proof here is a mechanical copy of the record's (Assembly.lean:877–1010,
Assembly/Certificate.lean) with `D0 T` replaced by a free `D`. No new mathematics.
-/
import Zeta23.Assembly.Certificate

open Filter Asymptotics Topology Real RHLinalg Set

noncomputable section

namespace Zeta23

/-- I′(D) := (T − D, 2T + D]  ([eq:D0] at a free buffer). `IprimeD T (D0 T) = Iprime T`. -/
def IprimeD (T D : ℝ) : Set ℝ := Set.Ioc (T - D) (2 * T + D)

lemma IprimeD_sqrtT (T : ℝ) : IprimeD T (D0 T) = Iprime T := rfl

namespace ZeroConfig

variable (Z : ZeroConfig)

/-- 𝒵(I′(D)): distinct zeros with ordinate in (T − D, 2T + D]. -/
def ZIprimeD (T D : ℝ) : Set ℂ := Z.window (T - D) (2 * T + D)

lemma ZIprimeD_sqrtT (T : ℝ) : Z.ZIprimeD T (D0 T) = Z.ZIprime T := rfl

/-- 𝒮₁ at buffer D: simple on-line zeros of 𝒵(I′(D)). -/
def S1D (T D : ℝ) : Set ℂ := Z.ZIprimeD T D ∩ onLine ∩ Z.simple

lemma S1D_sqrtT (T : ℝ) : Z.S1D T (D0 T) = Z.S1 T := rfl

/-- 𝒮₂ at buffer D: multiple on-line zeros of 𝒵(I′(D)). -/
def S2D (T D : ℝ) : Set ℂ := Z.ZIprimeD T D ∩ onLine ∩ {ρ | 2 ≤ Z.mult ρ}

lemma S2D_sqrtT (T : ℝ) : Z.S2D T (D0 T) = Z.S2 T := rfl

/-- off-line points of 𝒵(I′(D)). -/
def offLineD (T D : ℝ) : Set ℂ := Z.ZIprimeD T D ∩ {ρ | ρ.re ≠ 1 / 2}

lemma offLineD_sqrtT (T : ℝ) : Z.offLineD T (D0 T) = Z.offLine T := rfl

/-- s₁ at buffer D. -/
def s1D (T D : ℝ) : ℕ := (Z.S1D T D).ncard

lemma s1D_sqrtT (T : ℝ) : Z.s1D T (D0 T) = Z.s1 T := rfl

/-- s₂ at buffer D. -/
def s2D (T D : ℝ) : ℕ := (Z.S2D T D).ncard

lemma s2D_sqrtT (T : ℝ) : Z.s2D T (D0 T) = Z.s2 T := rfl

/-- p at buffer D: unordered off-line pairs {ρ, 1−ρ̄} in 𝒵(I′(D)). -/
def pD (T D : ℝ) : ℕ := (Z.offLineD T D).ncard / 2

lemma pD_sqrtT (T : ℝ) : Z.pD T (D0 T) = Z.p T := rfl

/-- N(I′(D)) := N(T − D, 2T + D). -/
def NIprimeD (T D : ℝ) : ℕ := Z.N (T - D) (2 * T + D)

lemma NIprimeD_sqrtT (T : ℝ) : Z.NIprimeD T (D0 T) = Z.NIprime T := rfl

/-- N_on(I′(D)). -/
def NonIprimeD (T D : ℝ) : ℕ := Z.N0 (T - D) (2 * T + D)

lemma NonIprimeD_sqrtT (T : ℝ) : Z.NonIprimeD T (D0 T) = Z.NonIprime T := rfl

end ZeroConfig

namespace Assembly

section WindowsD
open Set

variable (Z : ZeroConfig)

/-- N(I′(D)∖I) := N(T−D, T) + N(2T, 2T+D)  (the record's `NII` at a free buffer;
`NIID Z T (D0 T) = NII Z T`). -/
def NIID (T D : ℝ) : ℕ := Z.N (T - D) T + Z.N (2 * T) (2 * T + D)

lemma NIID_sqrtT (T : ℝ) : NIID Z T (D0 T) = NII Z T := rfl

variable {T D : ℝ}

/-- "`N(I′) = N(T,2T) + N(I′∖I)`" at a free buffer (mirror of `NIprime_eq`). -/
theorem NIprimeD_eq (hT : 0 ≤ T) (hD : 0 ≤ D) :
    Z.NIprimeD T D = Z.N T (2 * T) + NIID Z T D := by
  unfold ZeroConfig.NIprimeD NIID
  rw [N_add Z (b := T) (by linarith) (by linarith),
    N_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  ring

/-- `s₁ + s₂ = N₀*(T−D, 2T+D)` (mirror of `s1_add_s2_eq`; no sign condition needed). -/
theorem s1D_add_s2D_eq : Z.s1D T D + Z.s2D T D = Z.N0star (T - D) (2 * T + D) := by
  unfold ZeroConfig.s1D ZeroConfig.s2D ZeroConfig.N0star
  have hfin : (Z.ZIprimeD T D ∩ ZeroConfig.onLine).Finite :=
    (Z.window_finite _ _).subset inter_subset_left
  have hdisj : Disjoint (Z.S1D T D) (Z.S2D T D) := by
    rw [Set.disjoint_left]
    rintro ρ ⟨_, h1⟩ ⟨_, h2⟩
    simp only [ZeroConfig.simple, mem_setOf_eq] at h1 h2
    omega
  have hunion : Z.S1D T D ∪ Z.S2D T D = Z.ZIprimeD T D ∩ ZeroConfig.onLine := by
    ext ρ
    simp only [ZeroConfig.S1D, ZeroConfig.S2D, ZeroConfig.simple, mem_union, mem_inter_iff,
      mem_setOf_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · rintro ⟨h1, h2⟩
      have : 1 ≤ Z.mult ρ := Z.one_le_mult ρ (Z.window_subset_carrier _ _ h1)
      rcases this.eq_or_lt with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, h.symm⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
  rw [← Set.ncard_union_eq hdisj (hfin.subset (hunion ▸ subset_union_left))
    (hfin.subset (hunion ▸ subset_union_right)), hunion]
  rfl

/-- "`s₁ + s₂ ≤ N₀*(T,2T) + N(I′∖I)`" at a free buffer (mirror of `s1_add_s2_le`). -/
theorem s1D_add_s2D_le (hT : 0 ≤ T) (hD : 0 ≤ D) :
    Z.s1D T D + Z.s2D T D ≤ Z.N0star T (2 * T) + NIID Z T D := by
  rw [s1D_add_s2D_eq]
  rw [N0star_add Z (b := T) (by linarith) (by linarith),
    N0star_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NIID
  have h1 := (Z.N0star_le_Nd (T - D) T).trans (Z.Nd_le_N _ _)
  have h2 := (Z.N0star_le_Nd (2 * T) (2 * T + D)).trans (Z.Nd_le_N _ _)
  omega

/-- "`s₁ ≤ N₀ˢ(T,2T) + N(I′∖I)`" at a free buffer (mirror of `s1_le`). -/
theorem s1D_le (hT : 0 ≤ T) (hD : 0 ≤ D) :
    Z.s1D T D ≤ Z.N0s T (2 * T) + NIID Z T D := by
  have hs1 : Z.s1D T D = Z.N0s (T - D) (2 * T + D) := rfl
  rw [hs1, N0s_add Z (b := T) (by linarith) (by linarith),
    N0s_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NIID
  have c1 := Z.trivial_chain (T - D) T
  have c2 := Z.trivial_chain (2 * T) (2 * T + D)
  have h1 : Z.N0s (T - D) T ≤ Z.N (T - D) T := c1.1.trans (c1.2.1.trans c1.2.2.1)
  have h2 : Z.N0s (2 * T) (2 * T + D) ≤ Z.N (2 * T) (2 * T + D) :=
    c2.1.trans (c2.2.1.trans c2.2.2.1)
  omega

/-- "`#𝒵(I′) ≤ N_d(T,2T) + N(I′∖I)`" at a free buffer (mirror of `card_ZIprime_le`). -/
theorem card_ZIprimeD_le (hT : 0 ≤ T) (hD : 0 ≤ D) :
    (Z.ZIprimeD T D).ncard ≤ Z.Nd T (2 * T) + NIID Z T D := by
  have h : (Z.ZIprimeD T D).ncard = Z.Nd (T - D) (2 * T + D) := rfl
  rw [h, Nd_add Z (b := T) (by linarith) (by linarith),
    Nd_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  unfold NIID
  have h1 := Z.Nd_le_N (T - D) T
  have h2 := Z.Nd_le_N (2 * T) (2 * T + D)
  omega

end WindowsD

/-- The §6 moment certificate with the buffer count ABSTRACTED: identical to the record's
`count_certificate`, with `(NII Z T : ℝ)` replaced by a free `NIIf : ℝ → ℝ` throughout.
The record's proof never consumes the definition of `NII` — only its o(N) hypothesis —
so this is the same proof verbatim. Instantiating `NIIf T := (NIID Z T D T : ℝ)` (any
buffer profile `D : ℝ → ℝ`) yields the certificate at free D₀; `NIIf T := (NII Z T : ℝ)`
recovers the record's statement. -/
theorem count_certificate_free (Z : ZeroConfig) (P : Params) (κ : ℝ) (lower : ℝ → ℝ)
    (θ₀ : ℝ → ℝ) (NIIf : ℝ → ℝ)
    (h0 : ∀ᶠ T in atTop, 4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * NIIf T
      - θ₀ T / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ lower T)
    (hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T))
    (hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0))
    (hNII_o : NIIf =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)))
    (hNtop : Tendsto (fun T => (Z.N T (2 * T) : ℝ)) atTop atTop)
    (htrace : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (P.hat T (Z.Gz P T)))
    (hfrob : ∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * (Z.N T (2 * T) : ℝ) ≤ lower T := by
  intro ε hε
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by simp only [hδdef]; linarith
  have hκδ0 : 0 ≤ κ + δ := by
    by_contra h
    rw [not_le] at h
    obtain ⟨T, hT1, hT2⟩ := ((hfrob δ hδ).and (hNtop.eventually_ge_atTop 1)).exists
    have : frobSq (P.hat T (Z.Gz P T)) < 0 :=
      lt_of_le_of_lt hT1 (mul_neg_of_neg_of_pos h (by simp only [hNdef] at hT2 ⊢; linarith))
    exact absurd (frobSq_nonneg _) (not_le.mpr this)
  have hot := err_isLittleO (N := N) (R₁ := fun _ => 0) (R₂ := fun _ => 0)
    (NII := NIIf) (B := B) (cl := fun _ => κ + δ) (K := κ + δ)
    hNtop (isLittleO_zero _ _) (isLittleO_zero _ _) hNII_o hBto
    (Eventually.of_forall fun _ => ⟨hκδ0, le_rfl⟩)
  have hsmall : ∀ᶠ T in atTop,
      3 * NIIf T + B T * (4 + 2 * Real.sqrt ((κ + δ) * N T) + B T) ≤ δ * N T := by
    filter_upwards [hot.def hδ, hNtop.eventually_ge_atTop 0] with T h1 hN0
    simp only [Real.norm_eq_abs, mul_zero, zero_add, add_zero, abs_of_nonneg hN0] at h1
    exact (le_abs_self _).trans h1
  have hmain : ∀ᶠ T in atTop, (2 - κ - ε) * N T ≤ lower T := by
    filter_upwards [h0, hB0, htrace δ hδ, hfrob δ hδ, hsmall,
      hNtop.eventually_ge_atTop 0] with T hA hB₀ htr hfr hsm hN0
    have hlow := N0star_lower_moment (κ := κ) (R₁ := δ * N T) (R₂ := δ * N T) hB₀ hA
      (by simp only [hNdef] at htr ⊢; linarith) (by simp only [hNdef] at hfr ⊢; linarith)
    rw [show κ * N T + δ * N T = (κ + δ) * N T by ring] at hlow
    have hfin : (2 - κ - ε) * N T
        = (2 - κ) * N T - (4 * (δ * N T) + δ * N T + δ * N T) := by
      simp only [hδdef]; ring
    rw [hfin]
    linarith [hsm, hlow]
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmain
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end Assembly
end Zeta23

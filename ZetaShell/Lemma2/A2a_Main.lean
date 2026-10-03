/-
A2a_Main (L7_8, round 2, 28 Sep 2026): **Lemma 2(a)** (lem:shell-2 (a), sec_shell.tex l.283–292) assembled from its
step nodes, Lemma P and the `H_w` normalisation. The composition (Steps 0 and 5's bookkeeping, the bracket
arithmetic) is proved here; the open leaves are `step3_count`, `step4_profile`, `step5_window` (L7_8 nodes),
`lemmaP`, `Hw_normalisation`.

**Statement change (round 2).** `∃ Q₀, ∀ Q ≥ Q₀` replaces `∀ Q ≥ 2`. The round-1 form is false at `Q = 2`: there
`φ*(2) = 0`, so `H_w = 0` for all three families, while `R₁ = 1`, `K = 1`, `θ = 1/2` satisfy all hypotheses and
`D^Ω_δ(1/2) ≥ Ω(2)/δ > 0` (sharp: `Ω(2) = 1/2`), so `|D − H_w| ≤ B·H_w·bracket = 0` fails. The draft's lemma is
asymptotic, so this is a precision, not a change of content.
-/
import ZetaShell.Lemma2.A2a_S3_Count
import ZetaShell.Lemma2.A2a_S4_Profile
import ZetaShell.Lemma2.A2a_S5_Window
import ZetaShell.Lemma2.A2a_S0_Lines
import ZetaShell.Lemma2.A2_FareyBasics

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

theorem eventually_log_small (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∃ Q1 : ℝ, ∀ x : ℝ, Q1 ≤ x → Real.log x ^ n ≤ c * x := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := n)).def hc
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp h
  refine ⟨max a 0, fun x hx => ?_⟩
  have h1 := ha x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 ≤ x := le_trans (le_max_right _ _) hx
  simp only [Real.norm_eq_abs, id] at h1
  calc Real.log x ^ n ≤ |Real.log x ^ n| := le_abs_self _
    _ ≤ c * |x| := h1
    _ = c * x := by rw [abs_of_nonneg hx0]

/-- Step 0 in the form used here: the Dirichlet approximation `a/r` of `θ` gives a Farey point of level `Q`, and
`θ ∉ 𝒮` gives `u = rQ|η| ≥ K`. -/
theorem step0_u_ge_K (Q : ℕ) (K R1 θ : ℝ) (a r : ℤ) (hr1 : 1 ≤ r) (hrQ : (r : ℝ) ≤ Q)
    (hrR : (r : ℝ) ≤ R1) (hgcd : Int.gcd a r = 1) (hQ : 0 < (Q : ℝ))
    (hθ : θ ∉ shellSet Q K R1) : K ≤ (r : ℝ) * Q * |θ - (a : ℝ) / r| := by
  have hr0 : (0 : ℤ) < r := by omega
  have hrR' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hm0 : 0 ≤ a % r := Int.emod_nonneg a (by omega)
  have hmlt : a % r < r := Int.emod_lt_of_pos a hr0
  have hmn : (((a % r).toNat : ℕ) : ℤ) = a % r := Int.toNat_of_nonneg hm0
  have hrn : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg (by omega)
  have hrnR : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hrn
  have hmnR : (((a % r).toNat : ℕ) : ℝ) = ((a % r : ℤ) : ℝ) := by exact_mod_cast hmn
  set x0 : (_ : ℕ) × ℕ := ⟨r.toNat, (a % r).toNat⟩ with hx0def
  have hx0 : x0 ∈ fareyIdx Q := by
    rw [mem_fareyIdx]
    show (1 ≤ r.toNat ∧ r.toNat ≤ Q) ∧ (a % r).toNat < r.toNat ∧ Nat.Coprime (a % r).toNat r.toNat
    refine ⟨⟨by omega, ?_⟩, by omega, ?_⟩
    · have : ((r.toNat : ℕ) : ℝ) ≤ Q := by rw [hrnR]; exact hrQ
      exact_mod_cast this
    · rw [Nat.Coprime, ← Int.gcd_natCast_natCast, hmn, hrn, Int.gcd_emod]
      exact hgcd
  have hpt : fareyPt x0 = ((a % r : ℤ) : ℝ) / r := by
    simp only [fareyPt, hx0def]
    rw [hmnR, hrnR]
  have hdecomp : ((a % r : ℤ) : ℝ) + (r : ℝ) * ((a / r : ℤ) : ℝ) = (a : ℝ) := by
    have h := Int.emod_def a r
    have h' : ((a % r : ℤ) : ℝ) = ((a - r * (a / r) : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hdist : distZ (θ - fareyPt x0) ≤ |θ - (a : ℝ) / r| := by
    have h := distZ_le (θ - fareyPt x0) (a / r)
    have e : θ - fareyPt x0 - ((a / r : ℤ) : ℝ) = θ - (a : ℝ) / r := by
      rw [hpt, ← hdecomp]; push_cast; field_simp; ring
    rw [e] at h
    exact h
  have hnot : ¬ distZ (θ - fareyPt x0) < K / ((x0.1 : ℝ) * Q) := by
    intro hlt
    apply hθ
    exact ⟨x0, hx0, by simp only [hx0def]; rw [hrnR]; exact hrR, hlt⟩
  have hx01 : ((x0.1 : ℕ) : ℝ) = (r : ℝ) := by simp only [hx0def]; exact hrnR
  rw [hx01, not_lt] at hnot
  have hpos : 0 < (r : ℝ) * Q := by positivity
  have := le_trans hnot hdist
  rw [div_le_iff₀ hpos] at this
  linarith

set_option maxHeartbeats 1000000 in
/-- **A2(a) (lem:shell-2 (a)), corrected (`∃ Q₀`).** -/
theorem lemma2a (F : Fam) :
    ∃ B Q0 : ℝ, 0 ≤ B ∧ ∀ (Q : ℕ) (N ε K Omax θ : ℝ), Q0 ≤ Q → 0 < N → 0 < ε → 1 ≤ K →
      (∀ d ∈ Finset.Icc 1 Q, |ZetaShell.OmegaW Q (F.omega Q) d| ≤ Omax) →
      1 ≤ R1shell Q N ε → R1shell Q N ε ≤ (Q : ℝ) / (2 * K) → θ ∉ shellSet Q K (R1shell Q N ε) →
      |Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) (ε / N) θ - Hw F Q|
        ≤ B * Hw F Q * bracket2a Q N ε K Omax (Hw F Q) := by
  obtain ⟨C3, hC3, h3⟩ := step3_count F
  obtain ⟨C4, hC4, h4⟩ := step4_profile F
  obtain ⟨BP, hBP, hP⟩ := lemmaP F
  obtain ⟨C5, hC5, h5⟩ := step5_window F BP hBP hP
  obtain ⟨BH, hBH, hH⟩ := Hw_normalisation F
  have hg := gbar_pos F
  obtain ⟨Qa, hQa⟩ := eventually_log_small (1 / 3) (by norm_num) 6
  obtain ⟨Qb, hQb⟩ := eventually_log_small (gbar F / (2 * (BH + 1))) (by positivity) 2
  set K' := 14 * C3 + 2 * C4 + C5 + BH with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨1 + 2 * K' / gbar F, max (max Qa Qb) 3, by positivity, ?_⟩
  intro Q N ε K Omax θ hQ hN hε hK hOm hR1 hR1K hθ
  -- scalars
  have hQ3 : (3 : ℝ) ≤ Q := le_trans (le_max_right _ _) hQ
  have hQa' : Qa ≤ (Q : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQb' : Qb ≤ (Q : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQpos : (0 : ℝ) < Q := by linarith
  have hQn : 3 ≤ Q := by exact_mod_cast hQ3
  have hL1 : 1 ≤ Real.log Q := by
    have h1 : Real.exp 1 ≤ (Q : ℝ) := le_trans (le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))) hQ3
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hL6 : Real.log Q ^ 6 ≤ 1 / 3 * Q := hQa Q hQa'
  have hL2 : Real.log Q ^ 2 ≤ gbar F / (2 * (BH + 1)) * Q := hQb Q hQb'
  have hδ : 0 < ε / N := div_pos hε hN
  have hR1pos : 0 < R1shell Q N ε := by linarith
  have hKpos : 0 < K := by linarith
  have hR1Qδ : R1shell Q N ε * Q * (ε / N) = Real.log Q ^ 6 := by
    rw [R1shell]; field_simp
  have hR1half : 2 * R1shell Q N ε ≤ Q := by
    have h1 : (Q : ℝ) / (2 * K) ≤ Q / 2 := div_le_div_of_nonneg_left hQpos.le (by norm_num) (by linarith)
    linarith
  have hδ1 : ε / N < 1 := by
    have h1 : 1 * Q * (ε / N) ≤ R1shell Q N ε * Q * (ε / N) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR1 hQpos.le) hδ.le
    by_contra hcon
    have h2 : 1 * (Q : ℝ) ≤ (ε / N) * Q := mul_le_mul_of_nonneg_right (not_lt.mp hcon) hQpos.le
    linarith
  -- H_w
  have hHn := hH Q (by omega)
  have hHlow : gbar F * (Q : ℝ) ^ 2 / 2 ≤ Hw F Q := by
    have h1 := (abs_le.mp hHn).2
    have h2 : BH * Q * Real.log Q ^ 2 ≤ BH * Q * (gbar F / (2 * (BH + 1)) * Q) := by
      apply mul_le_mul_of_nonneg_left hL2 (by positivity)
    have hfrac : BH / (BH + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have e : BH * Q * (gbar F / (2 * (BH + 1)) * Q) = (BH / (BH + 1)) * (gbar F * (Q : ℝ) ^ 2 / 2) := by
      field_simp
    have h3 : (BH / (BH + 1)) * (gbar F * (Q : ℝ) ^ 2 / 2) ≤ gbar F * (Q : ℝ) ^ 2 / 2 :=
      mul_le_of_le_one_left (by positivity) hfrac
    linarith
  have hHpos : 0 < Hw F Q := lt_of_lt_of_le (by positivity) hHlow
  have hQ2H : (Q : ℝ) ^ 2 ≤ 2 / gbar F * Hw F Q := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hg]; linarith
  -- Step 0
  obtain ⟨a, r, hr1, hrR, hgcd, hη⟩ := dirichlet_reduced θ (R1shell Q N ε) hR1
  have hr0 : (0 : ℤ) < r := by omega
  have hrR' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrn : ((r.toNat : ℕ) : ℤ) = r := Int.toNat_of_nonneg (by omega)
  have hrnR : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast hrn
  have hrQ : (r : ℝ) ≤ Q := by linarith
  have huK := step0_u_ge_K Q K (R1shell Q N ε) θ a r hr1 hrQ hrR hgcd hQpos hθ
  have hθ' : θ = (a : ℝ) / ((r.toNat : ℕ) : ℝ) + (θ - (a : ℝ) / r) := by rw [hrnR]; ring
  have hrn1 : 1 ≤ r.toNat := by omega
  have hrnQ : r.toNat ≤ Q := by
    have : ((r.toNat : ℕ) : ℝ) ≤ Q := by rw [hrnR]; exact hrQ
    exact_mod_cast this
  have hη1 : |θ - (a : ℝ) / r| ≤ 1 / (r : ℝ) := by
    have : 1 / ((r : ℝ) * R1shell Q N ε) ≤ 1 / (r : ℝ) := by
      apply one_div_le_one_div_of_le hrR'
      exact le_mul_of_one_le_right hrR'.le hR1
    linarith
  -- the three step nodes
  have e3 := h3 Q r.toNat a (R1shell Q N ε) (θ - (a : ℝ) / r) (ε / N) (by omega) hrn1
    (by rw [hrnR]; exact hrR) hR1half (by rw [hrn]; exact hgcd) (by rw [hrnR]; exact hη) hδ hδ1
  have e4 := h4 Q r.toNat (θ - (a : ℝ) / r) (ε / N) (by omega) hrn1 hrnQ (by rw [hrnR]; exact hη1) hδ hδ1
  have e5 := h5 Q r.toNat (θ - (a : ℝ) / r) (ε / N) K (by omega) hrn1 hδ hK (by rw [hrnR]; exact huK)
  have hspike : |spike F Q r.toNat (θ - (a : ℝ) / r) (ε / N)| ≤ Omax := by
    rw [spike, abs_mul]
    have h1 := hOm r.toNat (Finset.mem_Icc.mpr ⟨hrn1, hrnQ⟩)
    have h2 : |(if |θ - (a : ℝ) / r| ≤ ε / N / 2 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    exact le_trans (mul_le_of_le_one_right (abs_nonneg _) h2) h1
  have hDX : Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) (ε / N) θ
      = (ε / N * Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) (ε / N)
          ((a : ℝ) / ((r.toNat : ℕ) : ℝ) + (θ - (a : ℝ) / r))) / (ε / N) := by
    rw [← hθ']; field_simp
  rw [hDX]
  have hOm0 : 0 ≤ Omax := le_trans (abs_nonneg _) (hOm 1 (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩))
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hbr : bracket2a Q N ε K Omax (Hw F Q)
      = (1 + Real.log K) ^ 3 / K + (Q * Real.log Q ^ 2 / ((ε / N) * R1shell Q N ε)) / (Q : ℝ) ^ 2
        + (Real.log Q ^ 8 / (ε / N)) / (Q : ℝ) ^ 2 + Omax / (ε / N) / Hw F Q := by
    unfold bracket2a
    field_simp
  rw [hbr]
  generalize hX : ε / N * Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) (ε / N)
      ((a : ℝ) / ((r.toNat : ℕ) : ℝ) + (θ - (a : ℝ) / r)) = X at e3 ⊢
  generalize hS : spike F Q r.toNat (θ - (a : ℝ) / r) (ε / N) = S at e3 hspike
  generalize hMs : mainSum F Q r.toNat (θ - (a : ℝ) / r) (ε / N) = Ms at e3 e4
  generalize hMp : mProf F Q r.toNat (θ - (a : ℝ) / r) (ε / N) = Mp at e4 e5
  have hrr : ((r.toNat : ℕ) : ℝ) ≤ R1shell Q N ε := by rw [hrnR]; exact hrR
  rw [hR1Qδ] at e3
  generalize hδd : ε / N = δ at *
  generalize hR1d : R1shell Q N ε = R1 at *
  generalize hLd : Real.log Q = L at *
  generalize hHd : Hw F Q = Hq at *
  generalize hrd : ((r.toNat : ℕ) : ℝ) = rr at *
  -- from here on: real arithmetic only
  have hJ1 : (1 : ℝ) ≤ Q / R1 + L ^ 6 + 1 := by
    have h0 : 0 ≤ (Q : ℝ) / R1 := by positivity
    have h1 : 0 ≤ L ^ 6 := by positivity
    linarith
  have hJpos : 0 < (Q : ℝ) / R1 + L ^ 6 + 1 := by linarith
  have hJle : (Q : ℝ) / R1 + L ^ 6 + 1 ≤ Real.exp 1 * Q := by
    have h1 : (Q : ℝ) / R1 ≤ Q := div_le_self hQpos.le hR1
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hQpos.le
    linarith
  have hlogJ : Real.log ((Q : ℝ) / R1 + L ^ 6 + 1) ≤ 1 + L := by
    have := Real.log_le_log hJpos hJle
    rw [Real.log_mul (Real.exp_pos 1).ne' hQpos.ne', Real.log_exp, hLd] at this
    linarith
  have hlJ0 : 0 ≤ 1 + Real.log ((Q : ℝ) / R1 + L ^ 6 + 1) := by
    have := Real.log_nonneg hJ1; linarith
  have hlogprod : (1 + Real.log ((Q : ℝ) / R1 + L ^ 6 + 1)) * (1 + L) ≤ 6 * L ^ 2 := by
    calc (1 + Real.log ((Q : ℝ) / R1 + L ^ 6 + 1)) * (1 + L) ≤ (3 * L) * (2 * L) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ = 6 * L ^ 2 := by ring
  have hLL2 : L ≤ L ^ 2 := le_self_pow₀ hL1 (by norm_num)
  have hL28 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL8 : 0 ≤ L ^ 8 := by positivity
  have hQ2t3 : L ^ 8 / δ = R1 * Q * L ^ 2 := by
    rw [div_eq_iff hδ.ne']
    have : L ^ 8 = L ^ 6 * L ^ 2 := by ring
    rw [this, ← hR1Qδ]; ring
  set t1 := (1 + Real.log K) ^ 3 / K with ht1
  set t2 := Q * L ^ 2 / (δ * R1) with ht2
  set t3 := L ^ 8 / δ with ht3
  have ht1n : 0 ≤ t1 := by positivity
  have ht2n : 0 ≤ t2 := by positivity
  have ht3n : 0 ≤ t3 := by positivity
  -- Step 3 error / δ
  have hb3 : |X - S - Ms| / δ ≤ C3 * (6 * t2 + 14 * t3) := by
    rw [div_le_iff₀ hδ]
    refine le_trans e3 ?_
    have hA : ((Q : ℝ) / R1 + L ^ 6 + 1) * (1 + Real.log ((Q : ℝ) / R1 + L ^ 6 + 1)) * (1 + L)
        ≤ ((Q : ℝ) / R1 + L ^ 6 + 1) * (6 * L ^ 2) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hlogprod hJpos.le
    have hB0 : rr * (1 + L) ≤ R1 * (2 * L ^ 2) :=
      mul_le_mul hrr (by linarith) (by linarith) hR1pos.le
    have hB : δ * Q * rr * (1 + L) ≤ δ * (2 * t3) := by
      rw [hQ2t3]
      have := mul_le_mul_of_nonneg_left hB0 (by positivity : (0 : ℝ) ≤ δ * Q)
      calc δ * Q * rr * (1 + L) = δ * Q * (rr * (1 + L)) := by ring
        _ ≤ δ * Q * (R1 * (2 * L ^ 2)) := this
        _ = δ * (2 * (R1 * Q * L ^ 2)) := by ring
    have hC : ((Q : ℝ) / R1 + L ^ 6 + 1) * (6 * L ^ 2) = δ * (6 * t2 + 6 * t3 + 6 * (L ^ 2 / δ)) := by
      rw [ht2, ht3]; field_simp
    have hD' : L ^ 2 / δ ≤ t3 := by rw [ht3]; exact div_le_div_of_nonneg_right hL28 hδ.le
    have hD'' : δ * (6 * t2 + 6 * t3 + 6 * (L ^ 2 / δ)) ≤ δ * (6 * t2 + 12 * t3) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le; linarith
    calc C3 * (((Q : ℝ) / R1 + L ^ 6 + 1) * (1 + Real.log ((Q : ℝ) / R1 + L ^ 6 + 1)) * (1 + L)
          + δ * Q * rr * (1 + L))
        ≤ C3 * (δ * (6 * t2 + 12 * t3) + δ * (2 * t3)) := by
          apply mul_le_mul_of_nonneg_left _ hC3; linarith
      _ = C3 * (6 * t2 + 14 * t3) * δ := by ring
  have hb4 : |Ms - Mp| / δ ≤ C4 * (2 * t3) := by
    rw [div_le_iff₀ hδ]
    refine le_trans e4 ?_
    have h1 : 1 + L ≤ 2 * L ^ 8 := by linarith
    have h2 : L ^ 8 ≤ t3 := by
      rw [ht3, le_div_iff₀ hδ]
      have := mul_le_mul_of_nonneg_left hδ1.le hL8
      linarith
    have h3 : C4 * δ * (1 + L) ≤ C4 * δ * (2 * t3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hb5 : |Mp - δ * (Q : ℝ) ^ 2 * gbar F| / δ ≤ C5 * ((Q : ℝ) ^ 2 * t1) := by
    rw [div_le_iff₀ hδ]
    calc _ ≤ C5 * δ * (Q : ℝ) ^ 2 * ((1 + Real.log K) ^ 3 / K) := e5
      _ = C5 * ((Q : ℝ) ^ 2 * t1) * δ := by rw [ht1]; ring
  have hbH : |(Q : ℝ) ^ 2 * gbar F - Hq| ≤ BH * t3 := by
    refine le_trans hHn ?_
    rw [hQ2t3]
    have h1 : (Q : ℝ) * L ^ 2 ≤ R1 * (Q * L ^ 2) := le_mul_of_one_le_left (by positivity) hR1
    calc BH * Q * L ^ 2 = BH * (Q * L ^ 2) := by ring
      _ ≤ BH * (R1 * (Q * L ^ 2)) := mul_le_mul_of_nonneg_left h1 hBH
      _ = BH * (R1 * Q * L ^ 2) := by ring
  have hSd : |S| / δ ≤ Omax / δ := div_le_div_of_nonneg_right hspike hδ.le
  -- triangle inequality
  have hsplit : X / δ - Hq = (X - S - Ms) / δ + (Ms - Mp) / δ + (Mp - δ * (Q : ℝ) ^ 2 * gbar F) / δ + S / δ
      + ((Q : ℝ) ^ 2 * gbar F - Hq) := by
    field_simp; ring
  have htri : |X / δ - Hq| ≤ |X - S - Ms| / δ + |Ms - Mp| / δ + |Mp - δ * (Q : ℝ) ^ 2 * gbar F| / δ
      + |S| / δ + |(Q : ℝ) ^ 2 * gbar F - Hq| := by
    rw [hsplit]
    have a1 := abs_add_le ((X - S - Ms) / δ + (Ms - Mp) / δ + (Mp - δ * (Q : ℝ) ^ 2 * gbar F) / δ + S / δ)
      ((Q : ℝ) ^ 2 * gbar F - Hq)
    have a2 := abs_add_le ((X - S - Ms) / δ + (Ms - Mp) / δ + (Mp - δ * (Q : ℝ) ^ 2 * gbar F) / δ) (S / δ)
    have a3 := abs_add_le ((X - S - Ms) / δ + (Ms - Mp) / δ) ((Mp - δ * (Q : ℝ) ^ 2 * gbar F) / δ)
    have a4 := abs_add_le ((X - S - Ms) / δ) ((Ms - Mp) / δ)
    rw [abs_div, abs_of_pos hδ, abs_div, abs_of_pos hδ] at a4
    rw [abs_div, abs_of_pos hδ] at a3 a2
    linarith
  -- final
  have hQ2 : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  have e2 : (Q : ℝ) ^ 2 * (t2 / (Q : ℝ) ^ 2) = t2 := by field_simp
  have e3' : (Q : ℝ) ^ 2 * (t3 / (Q : ℝ) ^ 2) = t3 := by field_simp
  have hOmd : Omax / δ = Hq * (Omax / δ / Hq) := by field_simp
  have hOmn : 0 ≤ Omax / δ / Hq := by positivity
  set s := t1 + t2 / (Q : ℝ) ^ 2 + t3 / (Q : ℝ) ^ 2 with hs
  have hsn : 0 ≤ s := by positivity
  have hQs : (Q : ℝ) ^ 2 * s = (Q : ℝ) ^ 2 * t1 + t2 + t3 := by rw [hs, mul_add, mul_add, e2, e3']
  have hsum : |X / δ - Hq| ≤ K' * ((Q : ℝ) ^ 2 * s) + Hq * (Omax / δ / Hq) := by
    rw [hQs, ← hOmd, hK']
    have p1 := mul_nonneg hC3 ht2n
    have p2 := mul_nonneg hC3 ht3n
    have p3 := mul_nonneg hC3 (mul_nonneg hQ2.le ht1n)
    have p4 := mul_nonneg hC4 (mul_nonneg hQ2.le ht1n)
    have p5 := mul_nonneg hC4 ht2n
    have p6 := mul_nonneg hC5 ht2n
    have p7 := mul_nonneg hC5 ht3n
    have p8 := mul_nonneg hBH (mul_nonneg hQ2.le ht1n)
    have p9 := mul_nonneg hBH ht2n
    have p10 := mul_nonneg hC4 ht3n
    linarith [hb3, hb4, hb5, hbH, htri, hSd]
  have hfin : K' * ((Q : ℝ) ^ 2 * s) ≤ (2 * K' / gbar F) * Hq * s := by
    have := mul_le_mul_of_nonneg_right hQ2H hsn
    have h2 := mul_le_mul_of_nonneg_left this hK'0
    calc K' * ((Q : ℝ) ^ 2 * s) ≤ K' * (2 / gbar F * Hq * s) := h2
      _ = (2 * K' / gbar F) * Hq * s := by ring
  have hk : 0 ≤ 2 * K' / gbar F := by positivity
  have q1 := mul_nonneg hHpos.le hsn
  have q2 := mul_nonneg (mul_nonneg hk hHpos.le) hOmn
  have hexp : (1 + 2 * K' / gbar F) * Hq * (s + Omax / δ / Hq)
      = Hq * s + Hq * (Omax / δ / Hq) + (2 * K' / gbar F) * Hq * s
        + (2 * K' / gbar F) * Hq * (Omax / δ / Hq) := by ring
  rw [hexp]
  linarith [hsum, hfin]

/-- **Consumer form (eq:shell-assembly, region (i)).** `(D^Ω_δ)⁺ ≤ H_w (1 + E_g)`, `E_g = B·bracket`, `Q ≥ Q₀`. -/
theorem lemma2a_upper (F : Fam) :
    ∃ B Q0 : ℝ, 0 ≤ B ∧ ∀ (Q : ℕ) (N ε K Omax θ : ℝ), Q0 ≤ Q → 0 < N → 0 < ε → 1 ≤ K →
      (∀ d ∈ Finset.Icc 1 Q, |ZetaShell.OmegaW Q (F.omega Q) d| ≤ Omax) →
      1 ≤ R1shell Q N ε → R1shell Q N ε ≤ (Q : ℝ) / (2 * K) → θ ∉ shellSet Q K (R1shell Q N ε) →
      max (Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) (ε / N) θ) 0
        ≤ Hw F Q * (1 + B * bracket2a Q N ε K Omax (Hw F Q)) := by
  obtain ⟨B, Q0, hB, h⟩ := lemma2a F
  refine ⟨B, max Q0 2, hB, ?_⟩
  intro Q N ε K Omax θ hQ hN hε hK hOm hR1 hR1K hθ
  have hQ0 : Q0 ≤ (Q : ℝ) := le_trans (le_max_left _ _) hQ
  have hQ2 : (2 : ℝ) ≤ Q := le_trans (le_max_right _ _) hQ
  have h1 := h Q N ε K Omax θ hQ0 hN hε hK hOm hR1 hR1K hθ
  have hH := Hw_nonneg F Q
  have hQn : 2 ≤ Q := by exact_mod_cast hQ2
  have hOm0 : 0 ≤ Omax := le_trans (abs_nonneg _) (hOm 1 (by simp; omega))
  have hbr : 0 ≤ bracket2a Q N ε K Omax (Hw F Q) := by
    unfold bracket2a
    have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
    have hR : 0 ≤ R1shell Q N ε := le_trans zero_le_one hR1
    have t1 : 0 ≤ (1 + Real.log K) ^ 3 / K := by positivity
    have t2 : 0 ≤ N * Real.log Q ^ 2 / (ε * Q * R1shell Q N ε) := by positivity
    have t3 : 0 ≤ N * Real.log Q ^ 8 / (ε * (Q : ℝ) ^ 2) := by positivity
    have t4 : 0 ≤ Omax * N / (ε * Hw F Q) := by positivity
    linarith
  have hup : Ddens (fareyIdx Q) fareyPt (fareyWeight F Q) (ε / N) θ
      ≤ Hw F Q * (1 + B * bracket2a Q N ε K Omax (Hw F Q)) := by
    have := (abs_le.mp h1).2
    nlinarith
  have hnn : 0 ≤ Hw F Q * (1 + B * bracket2a Q N ε K Omax (Hw F Q)) := by positivity
  exact max_le hup hnn

end TrackF
end ZetaShell

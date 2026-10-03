/-
S1L_Eventually (L7_5b, 1 Oct 2026): leaf `S1_eventually` of S1 — on Theorem S's range, for all large `Q`:
`T ≥ 2`, `2KR₁ ≤ Q`, `R₁ ≤ e^{s₀}`, `K ≤ Q`. With `x = log Q`, `m = 6 + 2B`: `R₁ ≤ e^{s₀+1} x^{6+B}/Q`
(`1/ε ≤ x^B`), `e^{s₀} ≤ Q^{α′}`, and `2e x^m ≤ Q^{2−α′}`, `e x^m ≤ Q` for large `x`.
-/
import ZetaShell.ShellS.S1_Defs

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

theorem S1_eventually' (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (αp B : ℝ) (hα2 : αp < 2) (hB : 1 ≤ B) :
    ∀ᶠ Qn : ℕ in Filter.atTop, 2 ≤ twin Qn r0 ε0 ∧ 1 ≤ (Qn : ℝ) ∧ ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      2 * K * (R1S Qn ε s₀ : ℝ) ≤ Qn ∧ (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ ∧ K / Qn ≤ 1 := by
  have hδ : 0 < 2 - αp := by linarith
  have h1 := (tendsto_exp_mul_div_rpow_atTop (6 + 2 * B) (2 - αp) hδ).eventually_ge_atTop (2 * Real.exp 1)
  have h2 := (tendsto_exp_mul_div_rpow_atTop (6 + 2 * B) 1 one_pos).eventually_ge_atTop (Real.exp 1)
  have h3 := Filter.eventually_ge_atTop (2 : ℝ)
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log n) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (h1.and (h2.and h3))] with Qn hQn
  obtain ⟨hx1, hx2, hx3⟩ := hQn
  set x := Real.log Qn with hx
  have hxpos : 0 < x := by linarith
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hQpos : (0 : ℝ) < Qn := by
    rcases (Nat.cast_nonneg Qn : (0 : ℝ) ≤ Qn).lt_or_eq with h | h
    · exact h
    · exfalso; rw [hx, ← h, Real.log_zero] at hxpos; exact lt_irrefl _ hxpos
  have hQ : (Qn : ℝ) = Real.exp x := (Real.exp_log hQpos).symm
  have hQ1 : (1 : ℝ) ≤ Qn := by rw [hQ]; exact Real.one_le_exp hxpos.le
  set m := 6 + 2 * B with hm
  have hxm : 0 < x ^ m := Real.rpow_pos_of_pos hxpos _
  have hi : 2 * Real.exp 1 * x ^ m ≤ Real.exp ((2 - αp) * x) := by
    have := hx1; rw [le_div_iff₀ hxm] at this; exact this
  have hii : Real.exp 1 * x ^ m ≤ Real.exp x := by
    have := hx2; rw [le_div_iff₀ hxm, one_mul] at this; exact this
  refine ⟨?_, hQ1, ?_⟩
  · unfold twin
    calc (2 : ℝ) ≤ x := hx3
      _ = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (r0 + ε0) := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
  · intro K ε s₀ hR
    have hK := hR.K_le
    have hε := hR.eps_ge
    have hs := hR.s_le
    have hK2 := hR.K_ge
    have hxB : 0 < x ^ B := Real.rpow_pos_of_pos hxpos B
    have hxB1 : 1 ≤ x ^ B := Real.one_le_rpow hx1' (by linarith)
    have hεpos : 0 < ε := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos _) hε
    have hinvε : 1 / ε ≤ x ^ B := by
      rw [div_le_iff₀ hεpos]
      rw [Real.rpow_neg hxpos.le] at hε
      have := mul_le_mul_of_nonneg_left hε hxB.le
      rw [mul_inv_cancel₀ hxB.ne'] at this; linarith
    have hR1 : (R1S Qn ε s₀ : ℝ) ≤ Real.exp (s₀ + 1) * x ^ 6 * x ^ B / Qn := by
      unfold R1S
      have hnn : 0 ≤ Real.exp (s₀ + 1) * Real.log Qn ^ 6 / (ε * Qn) := by positivity
      refine (Nat.floor_le hnn).trans ?_
      calc Real.exp (s₀ + 1) * x ^ 6 / (ε * Qn) = Real.exp (s₀ + 1) * x ^ 6 * (1 / ε) / Qn := by
            field_simp
        _ ≤ Real.exp (s₀ + 1) * x ^ 6 * x ^ B / Qn := by gcongr
    have hx6 : x ^ 6 * x ^ B * x ^ B = x ^ m := by
      have h6 : x ^ (6 : ℕ) = x ^ (6 : ℝ) := (Real.rpow_natCast x 6).symm
      rw [hm, h6, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      congr 1; ring
    have hx6pos : 0 < x ^ 6 := by positivity
    have hx6' : x ^ 6 * x ^ B ≤ x ^ m := by
      rw [← hx6]; exact le_mul_of_one_le_right (by positivity) hxB1
    have hes : Real.exp (s₀ + 1) = Real.exp 1 * Real.exp s₀ := by rw [← Real.exp_add]; ring_nf
    have hesα : Real.exp s₀ ≤ Real.exp (αp * x) := Real.exp_le_exp.mpr hs
    have hR0 : (0 : ℝ) ≤ R1S Qn ε s₀ := Nat.cast_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · -- 2 K R₁ ≤ Q
      calc 2 * K * (R1S Qn ε s₀ : ℝ) ≤ 2 * x ^ B * (Real.exp (s₀ + 1) * x ^ 6 * x ^ B / Qn) := by
            gcongr
        _ = 2 * Real.exp 1 * (x ^ 6 * x ^ B * x ^ B) * Real.exp s₀ / Qn := by rw [hes]; ring
        _ ≤ Real.exp ((2 - αp) * x) * Real.exp (αp * x) / Qn := by
            rw [hx6]; gcongr
        _ = Qn := by
            rw [← Real.exp_add, hQ, div_eq_iff (Real.exp_pos x).ne', ← Real.exp_add]; ring_nf
    · -- R₁ ≤ e^{s₀}
      calc (R1S Qn ε s₀ : ℝ) ≤ Real.exp (s₀ + 1) * x ^ 6 * x ^ B / Qn := hR1
        _ = Real.exp s₀ * (Real.exp 1 * (x ^ 6 * x ^ B)) / Qn := by rw [hes]; ring
        _ ≤ Real.exp s₀ * (Real.exp 1 * x ^ m) / Qn := by gcongr
        _ ≤ Real.exp s₀ * Real.exp x / Qn := by gcongr
        _ = Real.exp s₀ := by rw [hQ]; field_simp
    · -- K ≤ Q
      rw [div_le_one hQpos]
      have hBm : x ^ B ≤ x ^ m := Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
      have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
      calc K ≤ x ^ B := hK
        _ ≤ x ^ m := hBm
        _ ≤ Real.exp 1 * x ^ m := le_mul_of_one_le_left hxm.le he1
        _ ≤ Real.exp x := hii
        _ = Qn := hQ.symm

end ShellS
end ZetaShell

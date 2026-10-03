/-
Node A2(b) (L7_8, 28 Sep 2026): **Lemma 2(b), the everywhere bound** (lem:shell-2 (b), sec_shell.tex l.293, proof
l.303–304).

Draft: "(b) (Everywhere.) `|D^Ω_δ(θ)| ≤ D^{|Ω|}_δ(θ) ≤ ‖Ω‖_∞(Q² + N/ε)`", with `δ = ε/N`; proof "Consecutive points
of `𝔉_Q` are `≥ Q⁻²` apart, so a window of length `δ` holds at most `δQ² + 1` points."

Lean form: any real weights `W` on the index set `fareyIdx Q` (the draft's `Ω_ω(d)` is the case `W ⟨d, b⟩ = Ω_ω(d)`),
`|W| ≤ Wmax` on `fareyIdx Q`, `0 ≤ Wmax`; any `δ > 0` and any `θ`; `D` is L7_6's `Ddens` (distance on `ℝ/ℤ`, closed
window). The draft's `N/ε` is `1/δ`. No upper bound on `δ` and no lower bound on `Q` are needed (`Q = 0`: empty sum).
Hypothesis `0 ≤ Wmax` is needed only when `Q = 0` (then the left side is `0`); for `Q ≥ 1` it follows from `hW`.
Consumer: A3 (`signed_gallagher`, L7_6), which needs `δ · D^{|W|}_δ(θ) ≤ Wmax(δQ² + 1)` for every `θ`; the assembly
(eq:shell-assembly, regions (ii) rings and (iv) `𝒳_δ`), which needs `(D^Ω_δ)⁺ ≤ ‖Ω‖_∞(Q² + N/ε)`.
Status: PROVED (sorry-free).
-/
import ZetaShell.Lemma2.A2_FareyBasics

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- the density is the window sum. -/
theorem Ddens_eq_win (Q : ℕ) (W : (_ : ℕ) × ℕ → ℝ) (δ θ : ℝ) :
    Ddens (fareyIdx Q) fareyPt W δ θ = δ⁻¹ * ∑ x ∈ fareyWin Q θ δ, W x := by
  unfold Ddens fareyWin
  rw [Finset.sum_filter]

/-- **A2(b), first inequality**: `|D^W_δ(θ)| ≤ D^{|W|}_δ(θ)`. -/
theorem Ddens_abs_le (Q : ℕ) (W : (_ : ℕ) × ℕ → ℝ) (δ θ : ℝ) (hδ : 0 < δ) :
    |Ddens (fareyIdx Q) fareyPt W δ θ| ≤ Ddens (fareyIdx Q) fareyPt (fun x => |W x|) δ θ := by
  rw [Ddens_eq_win, Ddens_eq_win, abs_mul, abs_of_pos (inv_pos.mpr hδ)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_pos.mpr hδ).le

/-- **A2(b), second inequality**: `D^{|W|}_δ(θ) ≤ Wmax (Q² + 1/δ)`. -/
theorem Ddens_absW_le (Q : ℕ) (W : (_ : ℕ) × ℕ → ℝ) (Wmax δ θ : ℝ) (hδ : 0 < δ) (hW0 : 0 ≤ Wmax)
    (hW : ∀ x ∈ fareyIdx Q, |W x| ≤ Wmax) :
    Ddens (fareyIdx Q) fareyPt (fun x => |W x|) δ θ ≤ Wmax * ((Q : ℝ) ^ 2 + 1 / δ) := by
  rw [Ddens_eq_win]
  have hsum : ∑ x ∈ fareyWin Q θ δ, |W x| ≤ ((fareyWin Q θ δ).card : ℝ) * Wmax := by
    have h := Finset.sum_le_card_nsmul (fareyWin Q θ δ) (fun x => |W x|) Wmax (by
      intro x hx
      unfold fareyWin at hx
      exact hW x (Finset.mem_filter.mp hx).1)
    rw [nsmul_eq_mul] at h
    exact h
  have hcard := fareyWin_card Q θ δ hδ.le
  have h2 : ((fareyWin Q θ δ).card : ℝ) * Wmax ≤ (δ * (Q : ℝ) ^ 2 + 1) * Wmax :=
    mul_le_mul_of_nonneg_right hcard hW0
  have e : δ⁻¹ * ((δ * (Q : ℝ) ^ 2 + 1) * Wmax) = Wmax * ((Q : ℝ) ^ 2 + 1 / δ) := by
    field_simp
  calc δ⁻¹ * ∑ x ∈ fareyWin Q θ δ, |W x| ≤ δ⁻¹ * ((δ * (Q : ℝ) ^ 2 + 1) * Wmax) :=
        mul_le_mul_of_nonneg_left (le_trans hsum h2) (inv_pos.mpr hδ).le
    _ = Wmax * ((Q : ℝ) ^ 2 + 1 / δ) := e

/-- **A2(b) (lem:shell-2 (b)).** For real weights `W` on `𝔉_Q` with `|W| ≤ Wmax`, every `δ > 0` and every `θ`:
`|D^W_δ(θ)| ≤ D^{|W|}_δ(θ) ≤ Wmax (Q² + 1/δ)`; with `δ = ε/N` the right side is `‖Ω‖_∞(Q² + N/ε)`. -/
theorem lemma2b (Q : ℕ) (W : (_ : ℕ) × ℕ → ℝ) (Wmax δ θ : ℝ) (hδ : 0 < δ) (hW0 : 0 ≤ Wmax)
    (hW : ∀ x ∈ fareyIdx Q, |W x| ≤ Wmax) :
    |Ddens (fareyIdx Q) fareyPt W δ θ| ≤ Ddens (fareyIdx Q) fareyPt (fun x => |W x|) δ θ ∧
      Ddens (fareyIdx Q) fareyPt (fun x => |W x|) δ θ ≤ Wmax * ((Q : ℝ) ^ 2 + 1 / δ) :=
  ⟨Ddens_abs_le Q W δ θ hδ, Ddens_absW_le Q W Wmax δ θ hδ hW0 hW⟩

/-- the form consumed by A3's proof: `Σ_ξ |W_ξ| 1[θ ∈ I_ξ] ≤ Wmax (δQ² + 1)` for every `θ` (no `δ⁻¹`). -/
theorem lemma2b_window (Q : ℕ) (W : (_ : ℕ) × ℕ → ℝ) (Wmax δ θ : ℝ) (hδ : 0 ≤ δ) (hW0 : 0 ≤ Wmax)
    (hW : ∀ x ∈ fareyIdx Q, |W x| ≤ Wmax) :
    ∑ x ∈ fareyIdx Q, (if distZ (fareyPt x - θ) ≤ δ / 2 then |W x| else 0)
      ≤ Wmax * (δ * (Q : ℝ) ^ 2 + 1) := by
  rw [← Finset.sum_filter]
  have h := Finset.sum_le_card_nsmul ((fareyIdx Q).filter (fun x => distZ (fareyPt x - θ) ≤ δ / 2))
    (fun x => |W x|) Wmax (by
      intro x hx
      exact hW x (Finset.mem_filter.mp hx).1)
  rw [nsmul_eq_mul] at h
  have hcard := fareyWin_card Q θ δ hδ
  unfold fareyWin at hcard
  calc _ ≤ _ := h
    _ ≤ (δ * (Q : ℝ) ^ 2 + 1) * Wmax := mul_le_mul_of_nonneg_right hcard hW0
    _ = Wmax * (δ * (Q : ℝ) ^ 2 + 1) := by ring

end TrackF
end ZetaShell

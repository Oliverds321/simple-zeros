/-
A2_InterfaceCheck (L7_8, 28 Sep 2026): the consumers' needs from Lemma 2, derived from the L7_8 nodes.
* A3 (L7_6's `signed_gallagher`, copied unchanged from `lean_work/L7_6/A3_SignedGallagher.lean`, sha256 33d97e21…6f8f):
  its proof uses Lemma 2(b) as `δ · D^{|W|}_δ(θ) ≤ Wmax (δQ² + 1)` for every `θ`, i.e. `D^{|W|}_{ε/N} ≤ Wmax(Q² + N/ε)`,
  under exactly A3's hypotheses (`0 < ε < N`, `0 ≤ Wmax`, `|W| ≤ Wmax` on `fareyIdx Q`). Derived below from
  `lemma2b`, `lemma2b_window` (sorry-free).
* eq:shell-assembly region (iii): `D^Ω_δ = 0` on the holes of `r ≤ R₁` minus `𝒳_δ` (`δ < |β| < 1/(rQ) − δ`), from
  `lemma2c_hole` (sorry-free).
* region (i): `lemma2a_upper` (in `A2a_OutsideShells`, sorry only through `lemma2a`).
-/
import ZetaShell.Farey.A3_SignedGallagher
import ZetaShell.Lemma2.A2b_DensityBound
import ZetaShell.Lemma2.A2c_Holes

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- A3's use of Lemma 2(b), in A3's own variables. -/
theorem A3_density_input (Q : ℕ) (N ε : ℝ) (hN : 0 < N) (hε : 0 < ε) (_hεN : ε < N)
    (W : (_ : ℕ) × ℕ → ℝ) (Wmax : ℝ) (hW0 : 0 ≤ Wmax) (hW : ∀ x ∈ fareyIdx Q, |W x| ≤ Wmax) (θ : ℝ) :
    Ddens (fareyIdx Q) fareyPt (fun x => |W x|) (ε / N) θ ≤ Wmax * ((Q : ℝ) ^ 2 + N / ε) ∧
    ∑ x ∈ fareyIdx Q, (if distZ (fareyPt x - θ) ≤ ε / N / 2 then |W x| else 0)
      ≤ Wmax * (ε / N * (Q : ℝ) ^ 2 + 1) := by
  have hδ : 0 < ε / N := div_pos hε hN
  refine ⟨?_, lemma2b_window Q W Wmax (ε / N) θ hδ.le hW0 hW⟩
  have h := (lemma2b Q W Wmax (ε / N) θ hδ hW0 hW).2
  rwa [one_div_div] at h

/-- region (iii) of eq:shell-assembly: the hole of `a/r ∈ 𝔉_Q` minus the `δ`-neighbourhood of `a/r, a/r ± 1/(rQ)`. -/
theorem assembly_region_iii (Q r a : ℕ) (hx0 : (⟨r, a⟩ : (_ : ℕ) × ℕ) ∈ fareyIdx Q)
    (W : (_ : ℕ) × ℕ → ℝ) (δ β : ℝ) (hδ : 0 ≤ δ) (h1 : δ < |β|) (h2 : |β| < 1 / ((r : ℝ) * Q) - δ) :
    Ddens (fareyIdx Q) fareyPt W δ ((a : ℝ) / r + β) = 0 :=
  lemma2c_hole Q r a hx0 W δ β (by linarith) (by linarith)

end TrackF
end ZetaShell

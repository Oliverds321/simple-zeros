/-
nodes/C08_KCosDerivs.lean — track C node C08 (L1_1b, 28 Sep 2026).
Depends on: C07a.
Expected proof size: ≤ 60 lines.
PROVED (L5_1, 28 Sep 2026). Imports C07a_SincDeriv.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C07a_SincDeriv

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma hd_m (x : ℝ) : HasDerivAt (fun y : ℝ => Real.pi * y - 4 / 5) (Real.pi * 1) x :=
  ((hasDerivAt_id' x).const_mul Real.pi).sub_const (4 / 5)

private lemma hd_p (x : ℝ) : HasDerivAt (fun y : ℝ => Real.pi * y + 4 / 5) (Real.pi * 1) x :=
  ((hasDerivAt_id' x).const_mul Real.pi).add_const (4 / 5)

theorem hasDerivAt_kCos (x : ℝ) : HasDerivAt kCos (kCos1 x) x := by
  have h := (((hasDerivAt_sinc (Real.pi * x - 4 / 5)).comp x (hd_m x)).add
    ((hasDerivAt_sinc (Real.pi * x + 4 / 5)).comp x (hd_p x))).div_const (2 * Real.sinc (4 / 5))
  have e : kCos1 x = (sinc1 (Real.pi * x - 4 / 5) * (Real.pi * 1) + sinc1 (Real.pi * x + 4 / 5) * (Real.pi * 1)) /
      (2 * Real.sinc (4 / 5)) := by unfold kCos1; ring
  rw [e]
  exact h

theorem hasDerivAt_kCos1 (x : ℝ) : HasDerivAt kCos1 (kCos2 x) x := by
  have h := ((((hasDerivAt_sinc1 (Real.pi * x - 4 / 5)).comp x (hd_m x)).add
    ((hasDerivAt_sinc1 (Real.pi * x + 4 / 5)).comp x (hd_p x))).const_mul Real.pi).div_const
      (2 * Real.sinc (4 / 5))
  have e : kCos2 x = Real.pi * (sinc2 (Real.pi * x - 4 / 5) * (Real.pi * 1) +
      sinc2 (Real.pi * x + 4 / 5) * (Real.pi * 1)) / (2 * Real.sinc (4 / 5)) := by unfold kCos2; ring
  rw [e]
  exact h

theorem contDiff_kCos : ContDiff ℝ 3 kCos := by
  have hm : ContDiff ℝ 3 (fun x : ℝ => Real.pi * x - 4 / 5) := by fun_prop
  have hp : ContDiff ℝ 3 (fun x : ℝ => Real.pi * x + 4 / 5) := by fun_prop
  exact ((contDiff_sinc.comp hm).add (contDiff_sinc.comp hp)).div_const _

theorem hasDerivAt_wK (x : ℝ) : HasDerivAt wK (2 * kCos x * kCos1 x) x := by
  have h := (hasDerivAt_kCos x).pow 2
  have e : (2 * kCos x * kCos1 x) = ((2 : ℕ) : ℝ) * kCos x ^ (2 - 1) * kCos1 x := by norm_num
  rw [e]
  exact h

theorem hasDerivAt_wK1 (x : ℝ) : HasDerivAt (fun x => 2 * kCos x * kCos1 x) (wK2 x) x := by
  have h := ((hasDerivAt_kCos x).const_mul 2).mul (hasDerivAt_kCos1 x)
  have e : wK2 x = 2 * kCos1 x * kCos1 x + 2 * kCos x * kCos2 x := by unfold wK2; ring
  rw [e]
  exact h

end ZetaS.CertV2

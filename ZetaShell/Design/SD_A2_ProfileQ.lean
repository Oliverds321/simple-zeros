/-
Node SD-A2 (L7_7, F1a): an L75 profile is in ZetaQ's profile class `ProfileQ` at its own bandwidth — the field
`Valid.profile` of the design point. Draft: ssec:shell-cert-53 (L75 side conditions); paper §2.2 (profile class).
Deps: SD-A1; L7_1's `ShellProfile.L75` (discharged for S53-L75 by L7_1 node R5, `S53L75_L75`). Difficulty E.
-/
import ZetaShell.Design.SD_A1_PolyEval

namespace ZetaShell

theorem ShellProfile.poly_eval_neg (S : ShellProfile) (t : ℝ) : S.poly.eval (-t) = S.poly.eval t := by
  rw [S.poly_eval, S.poly_eval]
  unfold ShellProfile.p
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : 2 * -t / (S.lam : ℝ) = -(2 * t / (S.lam : ℝ)) := by ring
  rw [e, Even.neg_pow ⟨(i : ℕ), by ring⟩]

theorem ShellProfile.profileQ_of_L75 (S : ShellProfile) (hL : S.L75) :
    ZetaQ.ParamsQ.ProfileQ S.poly (S.lam : ℝ) where
  even := S.poly_eval_neg
  bulk := by
    intro t ht
    have h0 : (0 : ℝ) ≤ (S.lam : ℝ) / 2 := le_trans (abs_nonneg t) ht
    have habs : S.poly.eval t = S.p |t| := by
      rcases le_total 0 t with h | h
      · rw [abs_of_nonneg h, S.poly_eval]
      · rw [abs_of_nonpos h, ← S.poly_eval_neg, S.poly_eval]
    rw [habs]
    have hmem1 : |t| ∈ Set.Icc (0 : ℝ) ((S.lam : ℝ) / 2) := ⟨abs_nonneg t, ht⟩
    have hmem2 : (S.lam : ℝ) / 2 ∈ Set.Icc (0 : ℝ) ((S.lam : ℝ) / 2) := ⟨h0, le_rfl⟩
    have hmono := hL.anti.antitoneOn hmem1 hmem2 ht
    exact le_trans hL.end_ge hmono
  le_one := by
    intro t ht
    rw [S.poly_eval]
    exact hL.le_one t ht
  antitone := by
    have e : (fun t : ℝ => S.poly.eval t) = S.p := funext S.poly_eval
    rw [e]
    exact hL.anti.antitoneOn

end ZetaShell

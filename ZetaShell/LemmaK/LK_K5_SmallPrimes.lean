/-
Node K5 (L7_3): Lemma K.5 (lem:K-S), small primes. Draft: "Put `a′_n := a_n 1{n = p^k, p > R₀}` and `a″ := a − a′`.
For `Q ≥ Q₀` and `N ≥ Q`, `‖a″(s)‖² ≤ (1 + 0.98195)/π² + 0.23 T²(log eN)² N^{−1/2} ≤ 1`."
**Range restricted (defect D3 of the report):** the draft's proof bounds the `k = 1, p ≤ R₀` part by
`(log R₀)²/(π²ℓ_K²) ≤ π⁻²` using `log R₀ ≤ λℒ − ℓ_K`, i.e. `s ≤ log 𝒳`; the statement "`N ≥ Q`" is wider than the
proof. Lemma K uses it only on `ℓ_K ≤ s ≤ log 𝒳 − 1`, so the node is stated on `ℓ_K ≤ s ≤ log 𝒳`, asymptotic form
(eventually in `Q`), with `T = (log Q)^{r+ε}`, `𝒳 = e^{λℒ}`, `a` read on `n ≤ ⌊𝒳⌋`.
Dependencies: `|D_T(v)| ≤ min(T, 2/|v|)`; `Σ_{p≤x} log p/p ≤ log x + O(1)` (Mertens; tree:
`Zeta23.FromPNTPlus.Mertens`); `Σ_p (log p)²/(p(p−1)) < ∞`; count of prime powers `p^k`, `k ≥ 2`, in `(N/e, eN)`.
Difficulty: M.
-/
import ZetaShell.Defs.LK_Defs
import ZetaShell.LemmaK.LK9_K5_Asym

noncomputable section
open Filter

namespace ZetaShell
namespace LemmaK

/-- **K5 (Lemma K.5), asymptotic form on the range where it is used.** -/
theorem small_primes_l2 (lam r ε : ℝ) (hlam1 : 1 < lam) (hlam2 : lam < 2) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∀ᶠ Qn : ℕ in atTop, ∀ s : ℝ,
      ellK (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) ≤ s →
      s ≤ Real.log (Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)) →
      ZetaQ.l2sq ⌊Xlam lam (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε)⌋₊
        (fun n => acoef (ZetaQ.Twin (Qn : ℝ) r ε) s n
          - aPrime (ZetaQ.Twin (Qn : ℝ) r ε) s (R0 (Qn : ℝ) (ZetaQ.Twin (Qn : ℝ) r ε) s) n) ≤ 1 := by
  exact K5Aux.small_primes_aux lam r ε hlam1 hlam2 hr hε

end LemmaK
end ZetaShell

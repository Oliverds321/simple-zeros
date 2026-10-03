/-
A2a_S2s_Defs (L7_8, round 3): objects for the split of `step2_line_count`.
* `Pg F Q r r' j e f g lo hi = Σ_{k : q = rk − r′j ∈ [lo,hi], g | k, f | q} w(qe/Q)` (one Möbius term, Step 2, l.323);
* `admissibleP r j f`: every `p | f` with `p | r` divides `j` (the non-emptiness condition of `S_g`,
  `admissible_exists`/`admissible_necessary`).
-/
import ZetaShell.Lemma2.A2a_StepDefs
import ZetaShell.Lemma2.A2a_S2_OneClass

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

def Pg (F : Fam) (Q : ℕ) (r r' j : ℤ) (e f g : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc ⌈(lo + r' * j) / r⌉ ⌊(hi + r' * j) / r⌋,
    if (g : ℤ) ∣ k ∧ (f : ℤ) ∣ r * k - r' * j then F.w (((r * k - r' * j : ℤ) : ℝ) * e / Q) else 0

def admissibleP (r j : ℤ) (f : ℕ) : Prop := ∀ p ∈ f.primeFactors, ((p : ℕ) : ℤ) ∣ r → ((p : ℕ) : ℤ) ∣ j

end TrackF
end ZetaShell

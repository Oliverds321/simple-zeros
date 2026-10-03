/-
A2a_StepDefs (L7_8, round 2, 28 Sep 2026): objects of the proof of Lemma 2(a), Steps 2–5 (sec_shell.tex l.305–355),
and `gbar_pos`.

* `Vstar F` = `‖w‖_∞ + Var(w)` (l.275): 2 (sharp), 3 (dyadic), 2 (weighted).
* `deltaProd r j f = ∏_{p|f} δ_p`, `δ_p = 1/p` (`p ∤ rj`), `1` (`p | (r,j)`), `0` otherwise (Step 2, l.332–333).
* `lineCount F Q r r' j e f lo hi = Σ_{k : (k,j)=1, q = rk − r′j ∈ [lo,hi], f | q} w(qe/Q)` (Step 1–2, `N_j(e,f)`).
* `lineInt F Q r j e η δ = ∫_{I_j} w(qe/Q) dq`, `I_j = {q ∈ [1,Q] : j/(qr) ∈ [η − δ/2, η + δ/2]}` (Step 1, l.312).
* `mainSum F Q r η δ = Σ_{0<|j|≤M} (φ(|j|)/|j|)(1/r) Σ_{1≤e≤Q} c_e 𝔈_{|j|,r}(e) lineInt` (the main term after Step 3),
  `M = ⌊rQ(|η| + δ/2)⌋ + 1` (all lines that meet the window, `line_j_bound`).
* `mProf F Q r η δ = ∫_{η−δ/2}^{η+δ/2} Q² g_r(rQ|β|) dβ` (Step 4, l.343–345).
* `spike F Q r η δ = Ω(r)·1[|η| ≤ δ/2]` (the `j = 0` term, l.319).
-/
import ZetaShell.Lemma2.A2a_OutsideShells

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace TrackF

def Vstar : Fam → ℝ
  | .sharp => 2
  | .dyadic => 3
  | .weighted => 2

def deltaProd (r j : ℤ) (f : ℕ) : ℝ :=
  ∏ p ∈ f.primeFactors,
    (if ¬ (p : ℤ) ∣ r ∧ ¬ (p : ℤ) ∣ j then 1 / (p : ℝ) else if (p : ℤ) ∣ r ∧ (p : ℤ) ∣ j then 1 else 0)

def lineCount (F : Fam) (Q : ℕ) (r r' j : ℤ) (e f : ℕ) (lo hi : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc ⌈(lo + r' * j) / r⌉ ⌊(hi + r' * j) / r⌋,
    if Int.gcd k j = 1 ∧ (f : ℤ) ∣ r * k - r' * j then F.w (((r * k - r' * j : ℤ) : ℝ) * e / Q) else 0

def lineInt (F : Fam) (Q r : ℕ) (j : ℤ) (e : ℕ) (η δ : ℝ) : ℝ :=
  ∫ q in {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (j : ℝ) / (q * r) ∧ (j : ℝ) / (q * r) ≤ η + δ / 2},
    F.w (q * e / Q)

def mainSum (F : Fam) (Q r : ℕ) (η δ : ℝ) : ℝ :=
  let M : ℤ := (⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ + 1 : ℕ)
  ∑ j ∈ (Finset.Icc (-M) M).filter (fun j => j ≠ 0),
    ((Nat.totient j.natAbs : ℝ) / j.natAbs) * (1 / (r : ℝ)) *
      ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * Ecoef F.kind r j.natAbs e * lineInt F Q r j e η δ

def mProf (F : Fam) (Q r : ℕ) (η δ : ℝ) : ℝ :=
  ∫ β in (η - δ / 2)..(η + δ / 2), (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * |β|)

def spike (F : Fam) (Q r : ℕ) (η δ : ℝ) : ℝ :=
  ZetaShell.OmegaW Q (F.omega Q) r * (if |η| ≤ δ / 2 then 1 else 0)

theorem Sconst_pos : 0 < Sconst := by
  have hs : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2
  have hsP : Summable (fun p : Nat.Primes => 2 * (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective Subtype.val_injective
  have hg : Summable (fun p : Nat.Primes => (-(1 / ((p : ℕ) : ℝ) ^ 2) - 1 / ((p : ℕ) : ℝ) ^ 3)) := by
    refine Summable.of_norm_bounded hsP (fun p => ?_)
    have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have h2 : 0 < 1 / ((p : ℕ) : ℝ) ^ 2 := by positivity
    have h3 : 0 < 1 / ((p : ℕ) : ℝ) ^ 3 := by positivity
    have h32 : 1 / ((p : ℕ) : ℝ) ^ 3 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    rw [Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hpos : ∀ p : Nat.Primes, 0 < 1 + (-(1 / ((p : ℕ) : ℝ) ^ 2) - 1 / ((p : ℕ) : ℝ) ^ 3) := by
    intro p
    have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have h2 : 1 / ((p : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : 1 / ((p : ℕ) : ℝ) ^ 3 ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hlog := Real.summable_log_one_add_of_summable hg
  have heq := Real.rexp_tsum_eq_tprod hpos hlog
  have e : Sconst = ∏' p : Nat.Primes, (1 + (-(1 / ((p : ℕ) : ℝ) ^ 2) - 1 / ((p : ℕ) : ℝ) ^ 3)) := by
    unfold Sconst
    congr 1
    funext p
    ring
  rw [e, ← heq]
  exact Real.exp_pos _

theorem gbar_pos (F : Fam) : 0 < gbar F := by
  cases F <;> simp only [gbar, Fam.kind, Fam.W1]
  · positivity
  · positivity
  · have := Sconst_pos; positivity

end TrackF
end ZetaShell

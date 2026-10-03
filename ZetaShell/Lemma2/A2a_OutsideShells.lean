/-
Node A2(a) (L7_8, 28 Sep 2026): **Lemma 2(a), local density outside shells** (lem:shell-2 (a), sec_shell.tex
l.283–292, proof l.305–355), and the normalisation `Q²ḡ_w = H_w(1 + O(V* log²Q/Q))` (end of the proof of Lemma P,
l.384–385, used in Step 4, l.349).

Draft: "Let `δ = ε/N`, `K → ∞`, and `R₁ = N(log Q)⁶/(εQ) ≤ Q/(2K)`. (a) (Outside shells.) Uniformly for `θ ∉ 𝒮`,
`D^Ω_δ(θ) = H_w(1 + ϑB_w[(1+log K)³/K + N(log Q)²/(εQR₁) + N(log Q)⁸/(εQ²) + ‖Ω‖_∞N/(εH_w)])`, `|ϑ| ≤ 1`, where
`B_w ≪ V*` is effective and depends only on `V*` and the kind." `𝒮 = ⋃_{r≤R₁}{|θ − a/r| < K/(rQ)}` (l.186).

Lean form:
* weights `𝒲_{b/d} = Ω_ω(d)` with L7_6's `ZetaShell.OmegaW` (lem:shell-1; copied module `A1_SignedFarey`, compiled
  here unchanged), `ω = Fam.omega F Q` (`ω(q) = w(q/Q)` plain, `(q/φ(q)) w(q/Q)` for `q/φ`);
  `H_w = Σ_{2≤q≤Q} ω(q) φ*(q)` with trunk `ZetaQ.phiStar`; `D` = L7_6's `Ddens` on `fareyIdx Q`.
* `‖Ω‖_∞` is replaced by any bound `Omax` for `|Ω_ω(d)|`, `1 ≤ d ≤ Q` (equivalent: the bound is monotone in `Omax`).
* `R₁` is the real number `N(log Q)⁶/(εQ)`; hypotheses `1 ≤ R₁` (**added**: Step 0 uses a Dirichlet approximation
  with denominator `≤ R₁`; it holds on the Shell zone, where `N ≥ e⁴Q`) and `R₁ ≤ Q/(2K)`; `1 ≤ K`; `Q ≥ 2`.
* the constant `B` depends only on the family (the three families are fixed, so "depends only on `V*` and the
  kind" is automatic).
* The draft's closing sentence "with `R₁` as above the bracket is `O((1+log K)³/K + (log Q)⁻⁴)`" holds only when
  additionally `N/ε ≤ Q²(log Q)⁻¹²` (third term); it is not part of the node (on the Shell zone `N ≤ Q^{5/3+o(1)}`).
Consumer: eq:shell-assembly region (i), upper side only: `(D^Ω_δ)⁺ ≤ H_w(1 + E_g)` — derived below
(`lemma2a_upper`, sorry only through `lemma2a`).
Status (round 2): definitions, `Hw_normalisation` (sorry, not L7_8's node), `Hw_nonneg`; `lemma2a` is in `A2a_Main.lean`.
L7_11 (28 Sep 2026): `Hw_normalisation` PROVED (no sorry, statement unchanged); inputs in `L711_QphiSum` and the trunk's
`ZetaQ.Normalisation.N2.Astar_bound`, `ZetaQ.phiStar_one` (module `ZetaQ.Zones`).
-/
import ZetaShell.Skeleton.A2P_LineProfile
import ZetaShell.Lemma2.A2_FareyBasics
import ZetaShell.Farey.A1_SignedFarey
import ZetaShell.Lemma2.L711_QphiSum
import ZetaQ.Zones

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- the family weight `ω(q)` at level `Q` (sec_shell l.276–277). -/
def Fam.omega (F : Fam) (Q : ℕ) (q : ℕ) : ℝ :=
  match F.kind with
  | .plain => F.w ((q : ℝ) / Q)
  | .qphi => ((q : ℝ) / (Nat.totient q : ℝ)) * F.w ((q : ℝ) / Q)

/-- the Farey weight `𝒲_{b/d} = Ω_ω(d)` (l.272). -/
def fareyWeight (F : Fam) (Q : ℕ) (x : (_ : ℕ) × ℕ) : ℝ := ZetaShell.OmegaW Q (F.omega Q) x.1

/-- `H_w = Σ_{q≥2} ω(q) φ*(q)` (l.279). -/
def Hw (F : Fam) (Q : ℕ) : ℝ := ∑ q ∈ Finset.Icc 2 Q, F.omega Q q * (ZetaQ.phiStar q : ℝ)

/-- `R₁ = N(log Q)⁶/(εQ)` (l.181). -/
def R1shell (Q : ℕ) (N ε : ℝ) : ℝ := N * Real.log Q ^ 6 / (ε * Q)

/-- the shell set `𝒮 = ⋃_{r ≤ R₁} {‖θ − a/r‖ < K/(rQ)}` (l.186). -/
def shellSet (Q : ℕ) (K R1 : ℝ) : Set ℝ :=
  {θ | ∃ x ∈ fareyIdx Q, (x.1 : ℝ) ≤ R1 ∧ distZ (θ - fareyPt x) < K / ((x.1 : ℝ) * Q)}

/-- the bracket of Lemma 2(a). -/
def bracket2a (Q : ℕ) (N ε K Omax H : ℝ) : ℝ :=
  (1 + Real.log K) ^ 3 / K + N * Real.log Q ^ 2 / (ε * Q * R1shell Q N ε)
    + N * Real.log Q ^ 8 / (ε * (Q : ℝ) ^ 2) + Omax * N / (ε * H)

-- Round 2: `lemma2a` (corrected: `∃ Q₀`) and `lemma2a_upper` moved to `A2a_Main.lean`, proved there from the
-- step nodes of `A2a_Steps.lean`, `lemmaP` and `Hw_normalisation`.

/-! ### L7_11: proof of `Hw_normalisation`, family by family.
Sharp and dyadic: from the trunk's `ZetaQ.Normalisation.N2.Astar_bound` (`|Σ_{q≤N}φ*(q) − (18/π⁴)N²| ≤
5N(1+log N)²`). Weighted: summation by parts against the sub-node `qphiA_bound` (L711_QphiSum). -/

open ZetaQ.Normalisation in
theorem Hw_sharp_eq (Q : ℕ) (hQ : 1 ≤ Q) : Hw .sharp Q = N2.Astar Q - 1 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1 : ∀ q ∈ Finset.Icc 2 Q,
      Fam.omega .sharp Q q * (ZetaQ.phiStar q : ℝ) = (ZetaQ.phiStar q : ℝ) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hle : (q : ℝ) / Q ≤ 1 := by rw [div_le_one hQ0]; exact_mod_cast hq.2
    simp only [Fam.omega, Fam.kind, Fam.w]
    rw [if_pos ⟨by positivity, hle⟩, one_mul]
  unfold Hw
  rw [Finset.sum_congr rfl h1]
  unfold N2.Astar
  have hI : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp), ZetaQ.phiStar_one]
  push_cast
  ring

open ZetaQ.Normalisation in
theorem Hw_dyadic_eq (Q : ℕ) (hQ : 2 ≤ Q) : Hw .dyadic Q = N2.Astar Q - N2.Astar (Q / 2) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1 : ∀ q ∈ Finset.Icc 2 Q, Fam.omega .dyadic Q q * (ZetaQ.phiStar q : ℝ)
      = if q ∈ Finset.Ioc (Q / 2) Q then (ZetaQ.phiStar q : ℝ) else 0 := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hle : (q : ℝ) / Q ≤ 1 := by rw [div_le_one hQ0]; exact_mod_cast hq.2
    simp only [Fam.omega, Fam.kind, Fam.w, Finset.mem_Ioc]
    by_cases hc : Q / 2 < q
    · have hlt : (1 : ℝ) / 2 < (q : ℝ) / Q := by
        rw [div_lt_div_iff₀ (by norm_num) hQ0]
        have : Q < 2 * q := by omega
        have : (Q : ℝ) < 2 * q := by exact_mod_cast this
        linarith
      rw [if_pos ⟨hlt, hle⟩, if_pos ⟨hc, hq.2⟩, one_mul]
    · have hnlt : ¬ ((1 : ℝ) / 2 < (q : ℝ) / Q) := by
        rw [div_lt_div_iff₀ (by norm_num) hQ0, not_lt]
        have : 2 * q ≤ Q := by omega
        have : (2 * q : ℝ) ≤ Q := by exact_mod_cast this
        linarith
      rw [if_neg (fun h => hnlt h.1), if_neg (fun h => hc h.1), zero_mul]
  unfold Hw
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_mem]
  have hint : Finset.Icc 2 Q ∩ Finset.Ioc (Q / 2) Q = Finset.Ioc (Q / 2) Q := by
    ext x; simp only [Finset.mem_inter, Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hint]
  unfold N2.Astar
  have hcons := Finset.sum_Ioc_consecutive (fun q => (ZetaQ.phiStar q : ℝ))
    (Nat.zero_le (Q / 2)) (Nat.div_le_self Q 2)
  have e1 : Finset.Icc 1 Q = Finset.Ioc 0 Q := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have e2 : Finset.Icc 1 (Q / 2) = Finset.Ioc 0 (Q / 2) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e1, e2]
  linarith

theorem c18_le_one : (18 / Real.pi ^ 4 : ℝ) ≤ 1 := by
  have h3 := Real.pi_gt_three
  have : (81 : ℝ) ≤ Real.pi ^ 4 := by nlinarith [sq_nonneg (Real.pi ^ 2 - 9)]
  rw [div_le_one (by positivity)]
  linarith

open ZetaQ.Normalisation in
theorem Hw_normalisation_sharp : ∀ Q : ℕ, 2 ≤ Q →
    |(Q : ℝ) ^ 2 * gbar .sharp - Hw .sharp Q| ≤ 43 * Q * Real.log Q ^ 2 := by
  intro Q hQ
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hA := N2.Astar_bound Q (by omega)
  rw [Hw_sharp_eq Q (by omega)]
  have hg : gbar .sharp = 18 / Real.pi ^ 4 := by simp only [gbar, Fam.kind, Fam.W1]; ring
  rw [hg]
  have h8 := one_add_log_sq_le_eight hQ2
  have h3 := log_sq_ge_third hQ2
  have hL : 0 ≤ Real.log Q ^ 2 := sq_nonneg _
  have e : (Q : ℝ) ^ 2 * (18 / Real.pi ^ 4) - (N2.Astar Q - 1)
      = -(N2.Astar Q - 18 / Real.pi ^ 4 * (Q : ℝ) ^ 2) + 1 := by ring
  rw [e]
  calc |-(N2.Astar Q - 18 / Real.pi ^ 4 * (Q : ℝ) ^ 2) + 1|
      ≤ |N2.Astar Q - 18 / Real.pi ^ 4 * (Q : ℝ) ^ 2| + 1 := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg, abs_one]
    _ ≤ 5 * Q * (1 + Real.log Q) ^ 2 + 1 := by linarith
    _ ≤ 43 * Q * Real.log Q ^ 2 := by nlinarith

open ZetaQ.Normalisation in
theorem Hw_normalisation_dyadic : ∀ Q : ℕ, 2 ≤ Q →
    |(Q : ℝ) ^ 2 * gbar .dyadic - Hw .dyadic Q| ≤ 100 * Q * Real.log Q ^ 2 := by
  intro Q hQ
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  set M : ℕ := Q / 2 with hM
  have hM1 : 1 ≤ M := by omega
  have hMQ : M ≤ Q := Nat.div_le_self Q 2
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hMRQ : (M : ℝ) ≤ Q := by exact_mod_cast hMQ
  have h2M : (Q : ℝ) ≤ 2 * M + 1 := by
    have : Q ≤ 2 * M + 1 := by omega
    exact_mod_cast this
  have h2M' : (2 * M : ℝ) ≤ Q := by
    have : 2 * M ≤ Q := by omega
    exact_mod_cast this
  have hA := N2.Astar_bound Q (by omega)
  have hAM := N2.Astar_bound M hM1
  rw [Hw_dyadic_eq Q hQ]
  have hg : gbar .dyadic = 3 / 4 * (18 / Real.pi ^ 4) := by simp only [gbar, Fam.kind, Fam.W1]; ring
  rw [hg]
  set c : ℝ := 18 / Real.pi ^ 4 with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := c18_le_one
  have h8 := one_add_log_sq_le_eight hQ2
  have h3 := log_sq_ge_third hQ2
  have hlogM : (1 + Real.log M) ^ 2 ≤ (1 + Real.log Q) ^ 2 := by
    have h0 : 0 ≤ Real.log M := Real.log_nonneg hMR1
    have := Real.log_le_log (by linarith) hMRQ
    nlinarith
  have hAM' : |N2.Astar M - c * (M : ℝ) ^ 2| ≤ 5 * Q * (1 + Real.log Q) ^ 2 := by
    refine hAM.trans ?_
    have : 0 ≤ (1 + Real.log M) ^ 2 := sq_nonneg _
    nlinarith
  have hsq : |(Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2| ≤ (Q : ℝ) := by
    rw [abs_le]; constructor <;> nlinarith
  have e : (Q : ℝ) ^ 2 * (3 / 4 * c) - (N2.Astar Q - N2.Astar M)
      = -(N2.Astar Q - c * (Q : ℝ) ^ 2) + (N2.Astar M - c * (M : ℝ) ^ 2)
        - c * ((Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2) := by ring
  rw [e]
  have hL : 0 ≤ Real.log Q ^ 2 := sq_nonneg _
  have hcq : |c * ((Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2)| ≤ (Q : ℝ) := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc c * |(Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2| ≤ 1 * (Q : ℝ) := by
          exact mul_le_mul hc1 hsq (abs_nonneg _) (by norm_num)
      _ = Q := one_mul _
  calc |-(N2.Astar Q - c * (Q : ℝ) ^ 2) + (N2.Astar M - c * (M : ℝ) ^ 2)
        - c * ((Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2)|
      ≤ |N2.Astar Q - c * (Q : ℝ) ^ 2| + |N2.Astar M - c * (M : ℝ) ^ 2|
        + |c * ((Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2)| := by
        have t1 := abs_add_le (-(N2.Astar Q - c * (Q : ℝ) ^ 2) + (N2.Astar M - c * (M : ℝ) ^ 2))
          (-(c * ((Q : ℝ) ^ 2 / 4 - (M : ℝ) ^ 2)))
        have t2 := abs_add_le (-(N2.Astar Q - c * (Q : ℝ) ^ 2)) (N2.Astar M - c * (M : ℝ) ^ 2)
        rw [abs_neg, ← sub_eq_add_neg] at t1
        rw [abs_neg] at t2
        linarith
    _ ≤ 5 * Q * (1 + Real.log Q) ^ 2 + 5 * Q * (1 + Real.log Q) ^ 2 + Q := by linarith
    _ ≤ 100 * Q * Real.log Q ^ 2 := by nlinarith

/-- the weighted family: the summand of `Hw` for `1 ≤ q ≤ Q` is `f(q)·a(q)`. -/
theorem Hw_weighted_eq (Q : ℕ) (hQ : 1 ≤ Q) :
    Hw .weighted Q = ∑ q ∈ Finset.Icc 1 Q, (1 - (q : ℝ) / Q) ^ 2 *
        (((q : ℝ) / (Nat.totient q : ℝ)) * (ZetaQ.phiStar q : ℝ)) - (1 - 1 / (Q : ℝ)) ^ 2 := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have h1 : ∀ q ∈ Finset.Icc 2 Q, Fam.omega .weighted Q q * (ZetaQ.phiStar q : ℝ)
      = (1 - (q : ℝ) / Q) ^ 2 * (((q : ℝ) / (Nat.totient q : ℝ)) * (ZetaQ.phiStar q : ℝ)) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hle : (q : ℝ) / Q ≤ 1 := by rw [div_le_one hQ0]; exact_mod_cast hq.2
    simp only [Fam.omega, Fam.kind, Fam.w]
    rw [if_pos ⟨by positivity, hle⟩]
    ring
  unfold Hw
  rw [Finset.sum_congr rfl h1]
  have hI : Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.sum_insert (by simp), ZetaQ.phiStar_one]
  simp

set_option maxHeartbeats 1000000 in
theorem Hw_normalisation_weighted : ∃ B : ℝ, 0 ≤ B ∧ ∀ Q : ℕ, 2 ≤ Q →
    |(Q : ℝ) ^ 2 * gbar .weighted - Hw .weighted Q| ≤ B * Q * Real.log Q ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := qphiA_bound
  refine ⟨3 * |Sconst| + 16 * C + 3, by positivity, ?_⟩
  intro Q hQ
  have hQ1 : 1 ≤ Q := by omega
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  set S : ℝ := Sconst with hS
  -- summation by parts
  set f : ℕ → ℝ := fun k => (1 - (k : ℝ) / Q) ^ 2 with hf
  set a : ℕ → ℝ := fun q => if q = 0 then 0 else ((q : ℝ) / (Nat.totient q : ℝ)) * (ZetaQ.phiStar q : ℝ)
    with ha
  have hfQ : f Q = 0 := by simp only [hf]; rw [div_self hQ0.ne']; ring
  have hA : ∀ k : ℕ, ∑ q ∈ Finset.range (k + 1), a q = qphiA k := by
    intro k
    unfold qphiA
    have h0 : a 0 = 0 := by simp [ha]
    have hh := sum_Icc_one_eq_range a k
    rw [h0, sub_zero] at hh
    rw [← hh]
    apply Finset.sum_congr rfl
    intro q hq
    have : q ≠ 0 := by rw [Finset.mem_Icc] at hq; omega
    simp [ha, this]
  have hsum : ∑ q ∈ Finset.Icc 1 Q, f q * a q = -∑ k ∈ Finset.range Q, (f (k + 1) - f k) * qphiA k := by
    rw [sum_Icc_one_eq_range, Finset.sum_range_succ, abel_range f a Q, hfQ]
    simp only [hA]
    simp [ha]
  have hHw : Hw .weighted Q = ∑ q ∈ Finset.Icc 1 Q, f q * a q - (1 - 1 / (Q : ℝ)) ^ 2 := by
    rw [Hw_weighted_eq Q hQ1]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have : q ≠ 0 := by rw [Finset.mem_Icc] at hq; omega
    simp [hf, ha, this]
  -- the difference `f (k+1) - f k`
  have hdf : ∀ k : ℕ, f (k + 1) - f k = -2 / (Q : ℝ) + (2 * (k : ℝ) + 1) / (Q : ℝ) ^ 2 := by
    intro k; simp only [hf]; push_cast; field_simp; ring
  have hdf_abs : ∀ k ∈ Finset.range Q, |f (k + 1) - f k| ≤ 2 / (Q : ℝ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkQ : (k : ℝ) + 1 ≤ Q := by exact_mod_cast hk
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have e1 : -2 / (Q : ℝ) = -(2 / (Q : ℝ)) := by ring
    have h2Q : 0 ≤ 2 / (Q : ℝ) := by positivity
    rw [hdf k, e1, abs_le]
    constructor
    · have : 0 ≤ (2 * k + 1) / (Q : ℝ) ^ 2 := by positivity
      linarith
    · have : (2 * k + 1) / (Q : ℝ) ^ 2 ≤ 2 / (Q : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hQ0]; nlinarith
      linarith
  -- split `qphiA k = (S/2) k² + E k`
  set E : ℕ → ℝ := fun k => qphiA k - S / 2 * (k : ℝ) ^ 2 with hE
  have hEb : ∀ k ∈ Finset.range Q, |E k| ≤ C * Q * (1 + Real.log Q) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hk0 : k = 0
    · subst hk0
      have hE0 : E 0 = 0 := by simp [hE, qphiA]
      rw [hE0, abs_zero]
      positivity
    · have hk1 : 1 ≤ k := by omega
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkQ : (k : ℝ) ≤ Q := by exact_mod_cast hk.le
      refine (hC k hk1).trans ?_
      have hlog : (1 + Real.log k) ^ 2 ≤ (1 + Real.log Q) ^ 2 := by
        have h0 : 0 ≤ Real.log k := Real.log_nonneg hkR
        have := Real.log_le_log (by linarith) hkQ
        nlinarith
      have : 0 ≤ (1 + Real.log k) ^ 2 := sq_nonneg _
      calc C * k * (1 + Real.log k) ^ 2 ≤ C * Q * (1 + Real.log k) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ this
            exact mul_le_mul_of_nonneg_left hkQ hC0
        _ ≤ C * Q * (1 + Real.log Q) ^ 2 := by
            apply mul_le_mul_of_nonneg_left hlog; positivity
  have hsplit : -∑ k ∈ Finset.range Q, (f (k + 1) - f k) * qphiA k
      = S / 2 * (-∑ k ∈ Finset.range Q, (f (k + 1) - f k) * (k : ℝ) ^ 2)
        - ∑ k ∈ Finset.range Q, (f (k + 1) - f k) * E k := by
    rw [mul_neg, Finset.mul_sum]
    have : ∀ k ∈ Finset.range Q, (f (k + 1) - f k) * qphiA k
        = S / 2 * ((f (k + 1) - f k) * (k : ℝ) ^ 2) + (f (k + 1) - f k) * E k := by
      intro k _; simp only [hE]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    ring
  -- the main polynomial sum
  have hP : -∑ k ∈ Finset.range Q, (f (k + 1) - f k) * (k : ℝ) ^ 2
      = (Q : ℝ) ^ 2 / 6 - 1 / 6 - ((Q : ℝ) - 1) * (2 * Q - 1) / (6 * Q) := by
    have : ∀ k ∈ Finset.range Q, (f (k + 1) - f k) * (k : ℝ) ^ 2
        = -2 / (Q : ℝ) * (k : ℝ) ^ 2 + 2 / (Q : ℝ) ^ 2 * (k : ℝ) ^ 3 + 1 / (Q : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
      intro k _; rw [hdf k]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, sum_range_sq, sum_range_cube]
    field_simp
    ring
  have hPb : |(-∑ k ∈ Finset.range Q, (f (k + 1) - f k) * (k : ℝ) ^ 2) - (Q : ℝ) ^ 2 / 6| ≤ (Q : ℝ) := by
    rw [hP]
    have h0 : 0 ≤ ((Q : ℝ) - 1) * (2 * Q - 1) / (6 * Q) := by
      apply div_nonneg _ (by positivity); nlinarith
    have h1 : ((Q : ℝ) - 1) * (2 * Q - 1) / (6 * Q) ≤ Q / 3 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    rw [abs_le]; constructor <;> nlinarith
  have hErr : |∑ k ∈ Finset.range Q, (f (k + 1) - f k) * E k| ≤ 2 * C * Q * (1 + Real.log Q) ^ 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ k ∈ Finset.range Q, |(f (k + 1) - f k) * E k| ≤ 2 / (Q : ℝ) * (C * Q * (1 + Real.log Q) ^ 2) := by
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (hdf_abs k hk) (hEb k hk) (abs_nonneg _) (by positivity)
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (Q : ℝ) * (2 / (Q : ℝ) * (C * Q * (1 + Real.log Q) ^ 2)) = 2 * C * Q * (1 + Real.log Q) ^ 2 := by
      field_simp
    rw [this]
  have hf1 : |(1 - 1 / (Q : ℝ)) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have : 0 ≤ 1 - 1 / (Q : ℝ) := by
      rw [sub_nonneg, div_le_one hQ0]; linarith
    have : 1 - 1 / (Q : ℝ) ≤ 1 := by have : 0 ≤ 1 / (Q : ℝ) := by positivity
                                     linarith
    nlinarith
  have hg : gbar .weighted = S / 12 := by simp only [gbar, Fam.kind, Fam.W1, hS]; ring
  rw [hg, hHw, hsum, hsplit]
  set P : ℝ := -∑ k ∈ Finset.range Q, (f (k + 1) - f k) * (k : ℝ) ^ 2 with hPdef
  set R : ℝ := ∑ k ∈ Finset.range Q, (f (k + 1) - f k) * E k with hRdef
  have e : (Q : ℝ) ^ 2 * (S / 12) - (S / 2 * P - R - (1 - 1 / (Q : ℝ)) ^ 2)
      = -(S / 2 * (P - (Q : ℝ) ^ 2 / 6)) + R + (1 - 1 / (Q : ℝ)) ^ 2 := by ring
  rw [e]
  have hSP : |S / 2 * (P - (Q : ℝ) ^ 2 / 6)| ≤ |S| * Q := by
    rw [abs_mul, abs_div, abs_two]
    have : |S| / 2 ≤ |S| := by have := abs_nonneg S; linarith
    exact mul_le_mul this hPb (abs_nonneg _) (abs_nonneg _)
  have h8 := one_add_log_sq_le_eight hQ2
  have h3 := log_sq_ge_third hQ2
  have hL : 0 ≤ Real.log Q ^ 2 := sq_nonneg _
  have hSa : 0 ≤ |S| := abs_nonneg S
  calc |-(S / 2 * (P - (Q : ℝ) ^ 2 / 6)) + R + (1 - 1 / (Q : ℝ)) ^ 2|
      ≤ |S / 2 * (P - (Q : ℝ) ^ 2 / 6)| + |R| + |(1 - 1 / (Q : ℝ)) ^ 2| := by
        have t1 := abs_add_le (-(S / 2 * (P - (Q : ℝ) ^ 2 / 6)) + R) ((1 - 1 / (Q : ℝ)) ^ 2)
        have t2 := abs_add_le (-(S / 2 * (P - (Q : ℝ) ^ 2 / 6))) R
        rw [abs_neg] at t2
        linarith
    _ ≤ |S| * Q + 2 * C * Q * (1 + Real.log Q) ^ 2 + 1 := by linarith
    _ ≤ (3 * |S| + 16 * C + 3) * Q * Real.log Q ^ 2 := by
        have hQL0 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 3 * (Q : ℝ))
        have hQL : (Q : ℝ) ≤ 3 * Q * Real.log Q ^ 2 := by
          have e : 3 * (Q : ℝ) * (1 / 3) = Q := by ring
          linarith
        have hCQ0 := mul_le_mul_of_nonneg_left h8 (by positivity : (0 : ℝ) ≤ 2 * C * Q)
        have hCQ : 2 * C * Q * (1 + Real.log Q) ^ 2 ≤ 16 * C * Q * Real.log Q ^ 2 := by
          have e : 2 * C * (Q : ℝ) * (8 * Real.log Q ^ 2) = 16 * C * Q * Real.log Q ^ 2 := by ring
          linarith
        have h1 : (1 : ℝ) ≤ 3 * Q * Real.log Q ^ 2 := by linarith
        have hS3 := mul_le_mul_of_nonneg_left hQL hSa
        have e2 : (3 * |S| + 16 * C + 3) * Q * Real.log Q ^ 2
            = |S| * (3 * Q * Real.log Q ^ 2) + 16 * C * Q * Real.log Q ^ 2 + 3 * Q * Real.log Q ^ 2 := by ring
        rw [e2]
        have h4 : (1 : ℝ) ≤ 3 * Q * Real.log Q ^ 2 := h1
        nlinarith

/-- **A2N (end of the proof of lem:shell-P, l.384–385).** `Q² ḡ_w = H_w (1 + O(log²Q/Q))`, in the additive form
`|Q² ḡ_w − H_w| ≤ B Q log²Q` (equivalent, since `H_w ≍ Q²`). Used in Step 4 of Lemma 2(a). -/
theorem Hw_normalisation (F : Fam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Q : ℕ, 2 ≤ Q →
      |(Q : ℝ) ^ 2 * gbar F - Hw F Q| ≤ B * Q * Real.log Q ^ 2 := by
  cases F with
  | sharp => exact ⟨43, by norm_num, Hw_normalisation_sharp⟩
  | dyadic => exact ⟨100, by norm_num, Hw_normalisation_dyadic⟩
  | weighted => exact Hw_normalisation_weighted

theorem Fam.w_nonneg (F : Fam) (x : ℝ) : 0 ≤ F.w x := by
  cases F <;> simp only [Fam.w] <;> split_ifs <;> positivity

theorem Fam.omega_nonneg (F : Fam) (Q q : ℕ) : 0 ≤ F.omega Q q := by
  have hw := F.w_nonneg ((q : ℝ) / Q)
  cases F <;> simp only [Fam.omega, Fam.kind] <;> first | exact hw | exact mul_nonneg (by positivity) hw

theorem Hw_nonneg (F : Fam) (Q : ℕ) : 0 ≤ Hw F Q :=
  Finset.sum_nonneg (fun q _ => mul_nonneg (F.omega_nonneg Q q) (by positivity))

end TrackF
end ZetaShell

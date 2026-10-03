/-
ZetaS/Cert/CertSpecAM5.lean — integrated by L0_1 (28 Sep 2026) from lean_work/L6_1/CertSpecAM5_patched.lean ( L1_1's CertSpecAM5 with the sorries of
nodes C23, C24, C25, C26 replaced by L6_1's proofs, same imports; only `Cert.check_sound` (C21) remains `sorry`;
added: `certAM5_of_checks_of_sound`, the assembly with C21 as a hypothesis) — what the K = 5 all-marks certificate proves (L1_1b, 28 Sep 2026).

Target (lead's decision, 28 Sep): the first hypothesis-free level-A pair, thm:zeta-allmarks data (X2, K = 5):
  simple zeros ≥ 0.675158622, distinct zeros ≥ 0.837579311 (`CosWindow.sigma_K5`, `CosWindow.dist_K5` of L0_2).

  `CertAM5` — stated exactly as L0_4's `CertAM7` (ChallengeZetaS.lean §4), with the K = 5 constants.
  `W5`      — the concrete witness: X2's weights (round1/X2_numerics/xpat_K5_*.json, claims_a1.6_K5_mu500.json).
  `classData j` — the checker instance (`LIQ`, checker v3) of the j-th canonical class (20 classes = reversal
              classes of {1,2}^5; node C-rev is PROVED by L2_2: `ZetaS.localCertAM_of_classes`).
  `Cert.check_sound` — the certificate theorem, over the WHOLE orthant g ≥ 0 (see the CAP argument below).
  `certAM5_of_checks` — the assembly: 20 checked certificates ⟹ `CertAM5`.

The CAP argument (placement: inside `Cert.check_sound`, discharged by the root conditions of `Cert.check`):
  `Cert.check` requires root = [0, u_0] × ⋯ × [0, u_3] with μ_l · u_l ≥ claim for every l, all γ' ≥ 0, μ ≥ 0.
  For g ≥ 0: either g ∈ root, and the tree covers it (Node soundness), or g_l > u_l for some l, and then
  F(g) ≥ μ_l g_l ≥ μ_l u_l ≥ claim because every other term of F is ≥ 0 (γ' ≥ 0, k² ≥ 0, μ ≥ 0, g ≥ 0).
  Inside the root, CAP leaves use the same inequality with Σ_l μ_l lo_l ≥ claim.
-/
import ZetaS.SigmaDist.C1_ReversalClasses
import ZetaS.Cert.CheckerCoreV3
import ZetaS.Top.TopDefs

set_option linter.dupNamespace false

noncomputable section

open Finset

namespace ZetaS.CertV2

/-! ## 1. The real side of the checker instance -/

/-- The Gram kernel of ψ = cos(1.6 s) in closed form. -/
def kCos (x : ℝ) : ℝ :=
  (Real.sinc (Real.pi * x - 4 / 5) + Real.sinc (Real.pi * x + 4 / 5)) / (2 * Real.sinc (4 / 5))

/-- span value g_i + ⋯ + g_{i+s−1} of a gap sequence. -/
def spanVal (g : ℕ → ℝ) (i s : ℕ) : ℝ := ∑ t ∈ Finset.range s, g (i + t)

/-- The real functional of a checker instance. -/
def LIQ.F (D : LIQ) (g : ℕ → ℝ) : ℝ :=
  (D.spans.map fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2).sum +
    ∑ l ∈ Finset.range D.d, ((D.mu.getD l 0 : ℚ) : ℝ) * g l

/-- What one certificate proves: the inequality on the whole orthant. -/
def LIQ.Holds (D : LIQ) : Prop := ∀ g : ℕ → ℝ, (∀ l, 0 ≤ g l) → ((D.claim : ℚ) : ℝ) ≤ D.F g

def LIQ.wf (D : LIQ) : Bool :=
  D.spans.all (fun sp => decide (0 ≤ sp.2.2) && decide (1 ≤ sp.2.1) && decide (sp.1 + sp.2.1 ≤ D.d)) &&
    D.mu.all (fun m => decide (0 ≤ m)) && decide (D.mu.length = D.d)

/-- A certificate: the instance, the root box, the tree. -/
structure Cert where
  data : LIQ
  root : Box
  tree : Node

/-- Root conditions (the CAP argument for the unbounded domain) + well-formedness + the tree. -/
def Cert.check (C : Cert) : Bool :=
  C.data.wf && decide (C.root.length = C.data.d) &&
    (List.range C.data.d).all (fun l => decide ((C.root.getD l (0, 0)).1 = 0) &&
      decide (C.data.claim ≤ C.data.mu.getD l 0 * (C.root.getD l (0, 0)).2)) &&
    C.tree.check C.data C.root

-- NOT IN THIS MODULE: `Cert.check_sound` (node C21). Its proof imports the C-nodes, which import this module through
-- NodeDefs, so it cannot live here. It is proved downstream against the fixed checker v3 (round 12, L0_5):
-- `ZetaS.CertV2.ChainV3.cert_check_sound` in ZetaS/Cert/ChainV3.lean (level A).
-- Historical note: the v2 checker (module CheckerCore, retired 28 Sep 2026) had an unsound LP leaf check
-- (L5_1's counterexample); v3 = CheckerBase + CheckerLeaves adds the x̂ guard in `lpSpan` (L1_1c).

/-! ## 2. The K = 5 data (X2) -/

/-- base pair weights γ_{s,i} (sec_zeta.tex def:zeta-LIm; xpat_K5_*.json `base_gam`, spans order (i,s)). -/
def gam5 : ℕ → ℕ → ℚ
  | 1, 0 => 3927 / 10000 | 1, 1 => 6073 / 10000 | 1, 2 => 6073 / 10000 | 1, 3 => 3927 / 10000
  | 2, 0 => 11787 / 20000 | 2, 1 => 8213 / 10000 | 2, 2 => 11787 / 20000
  | 3, 0 => 1 | 3, 1 => 1 | 4, 0 => 2
  | _, _ => 0

def mu5 : List ℚ := [3833 / 2500000, 6167 / 2500000, 6167 / 2500000, 3833 / 2500000]
def b5 : Fin 5 → Fin 2 → ℚ :=
  ![![64333 / 25000000, 310701 / 100000000], ![64617 / 25000000, 61913 / 20000000],
    ![248597 / 100000000, 79859 / 25000000], ![64617 / 25000000, 61913 / 20000000],
    ![64333 / 25000000, 310701 / 100000000]]

private theorem gam5_nonneg (s i : ℕ) : (0 : ℚ) ≤ gam5 s i := by
  unfold gam5
  split <;> norm_num

private theorem W5_gam_nonneg : ∀ s ∈ Finset.Icc 1 (5 - 1), ∀ i ∈ Finset.range (5 - s), (0 : ℝ) ≤ (gam5 s i : ℝ) := by
  intro s _ i _
  exact_mod_cast gam5_nonneg s i

private theorem W5_gam_sum : ∀ s ∈ Finset.Icc 1 (5 - 1), ∑ i ∈ Finset.range (5 - s), (gam5 s i : ℝ) = 2 := by
  intro s hs
  rw [Finset.mem_Icc] at hs
  obtain ⟨h1, h2⟩ := hs
  interval_cases s <;> norm_num [Finset.sum_range_succ, gam5]

private theorem W5_mu_nonneg : ∀ l : Fin (5 - 1), (0 : ℝ) ≤ ((mu5.getD l 0 : ℚ) : ℝ) := by
  intro l
  fin_cases l <;> norm_num [mu5]

/-- The witness `W5 : MarkWeights 5` (node C-W5: the four proof fields, by `norm_num`/`decide`). -/
def W5 : MarkWeights 5 where
  γ := fun s i => (gam5 s i : ℝ)
  μ := fun l => ((mu5.getD l 0 : ℚ) : ℝ)
  two_le := by norm_num
  γ_nonneg := W5_gam_nonneg
  γ_sum := W5_gam_sum
  μ_nonneg := W5_mu_nonneg
  b := fun i j => (b5 i j : ℝ)

/-- The 20 canonical classes (min of a pattern and its reversal), marks 1 ↦ 0, 2 ↦ 1. -/
def classes5 : List (List ℕ) :=
  [[1,1,1,1,1],[1,1,1,1,2],[1,1,1,2,1],[1,1,1,2,2],[1,1,2,1,1],[1,1,2,1,2],[1,1,2,2,1],[1,1,2,2,2],
   [1,2,1,1,2],[1,2,1,2,1],[1,2,1,2,2],[1,2,2,1,2],[1,2,2,2,1],[1,2,2,2,2],[2,1,1,1,2],[2,1,1,2,2],
   [2,1,2,1,2],[2,1,2,2,2],[2,2,1,2,2],[2,2,2,2,2]]

/-- The checker instance of a mark pattern `m` (list of marks in {1,2}): pattern weights γ_{s,i} m_i m_{i+s},
spans in the order of the data files ((i,s) for s = 1..4, i = 0..4−s), claim Σ_i b_i(m_i). -/
def classData (m : List ℕ) : LIQ :=
  ⟨4, ((List.range 4).flatMap fun s => (List.range (4 - s)).map fun i =>
        (i, s + 1, gam5 (s + 1) i * (m.getD i 1 : ℚ) * (m.getD (i + s + 1) 1 : ℚ))),
    mu5,
    ((List.range 5).map fun i => if h : i < 5 then b5 ⟨i, h⟩ (if m.getD i 1 = 2 then 1 else 0) else 0).sum⟩

-- `CertAM5` is defined once, in `ZetaS.Top.TopDefs` (lead's ruling, 28 Sep 2026); inside this namespace
-- the name `CertAM5` resolves to `ZetaS.CertAM5`.

/-- ∫_{−1/2}^{1/2} cos(a s) ds = sinc(a/2), for every real a. -/
private theorem integral_cos_mul_half (a : ℝ) :
    ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (a * s) = Real.sinc (a / 2) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one, zero_div,
      Real.sinc_zero]
    norm_num
  · rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) ha, integral_cos, smul_eq_mul,
      show a * -(1 / 2) = -(a / 2) by ring, show a * (1 / 2) = a / 2 by ring, Real.sin_neg,
      Real.sinc_of_ne_zero (div_ne_zero ha two_ne_zero), div_div_eq_mul_div]
    ring

/-- Node C-bridge-k: the closed form is the normalised Fourier transform of cos(1.6 s) (uses L0_2's
`CosWindow.integral_cosW` and the product-to-sum formula). -/
theorem kPsi_psiCos16_eq (x : ℝ) : kPsi psiCos16 x = kCos x := by
  unfold kPsi psiCos16 kCos
  have hpt : ∀ s, Real.cos (8 / 5 * s) * Real.cos (2 * Real.pi * x * s)
      = (Real.cos ((2 * Real.pi * x - 8 / 5) * s) + Real.cos ((2 * Real.pi * x + 8 / 5) * s)) / 2 := by
    intro s
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring
  have hc1 : Continuous fun s : ℝ => Real.cos ((2 * Real.pi * x - 8 / 5) * s) := by fun_prop
  have hc2 : Continuous fun s : ℝ => Real.cos ((2 * Real.pi * x + 8 / 5) * s) := by fun_prop
  have hnum : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) * Real.cos (2 * Real.pi * x * s)
      = (Real.sinc (Real.pi * x - 4 / 5) + Real.sinc (Real.pi * x + 4 / 5)) / 2 := by
    simp_rw [hpt]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _), integral_cos_mul_half, integral_cos_mul_half,
      show (2 * Real.pi * x - 8 / 5) / 2 = Real.pi * x - 4 / 5 by ring,
      show (2 * Real.pi * x + 8 / 5) / 2 = Real.pi * x + 4 / 5 by ring]
  have hden : ∫ s in (-(1 / 2 : ℝ))..(1 / 2), Real.cos (8 / 5 * s) = Real.sinc (4 / 5) := by
    rw [integral_cos_mul_half]
    norm_num
  rw [hnum, hden]
  ring

private theorem gapSpan_eq_spanVal (g : ℕ → ℝ) {i s : ℕ} (h : i + s ≤ 4) :
    gapSpan (K := 5) (fun l : Fin (5 - 1) => g l) i s = spanVal g i s := by
  unfold gapSpan spanVal
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun l => if i ≤ l ∧ l < i + s then g l else 0) (5 - 1),
    ← Finset.sum_filter]
  have hset : (Finset.range (5 - 1)).filter (fun l => i ≤ l ∧ l < i + s) = Finset.Ico i (i + s) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

private theorem mL_getD (m : Fin 5 → Fin 2) {i : ℕ} (hi : i < 5) :
    ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1).getD i 1 = (m ⟨i, hi⟩ : ℕ) + 1 := by
  simp [List.getD_eq_getElem?_getD, hi]

private theorem markVal_lt (m : Fin 5 → Fin 2) {i : ℕ} (hi : i < 5) : markVal m i = ((m ⟨i, hi⟩ : ℕ) : ℝ) + 1 := by
  unfold markVal
  rw [dif_pos hi]

/-- the span list of a class instance as a double Finset sum. -/
private theorem spans_sum (T : ℕ → ℕ → ℚ) (Φ : ℕ × ℕ × ℚ → ℝ) :
    (((List.range 4).flatMap fun s => (List.range (4 - s)).map fun i => (i, s + 1, T s i)).map Φ).sum
      = ∑ s ∈ Finset.range 4, ∑ i ∈ Finset.range (4 - s), Φ (i, s + 1, T s i) := by
  have r4 : List.range 4 = [0, 1, 2, 3] := rfl
  have r3 : List.range 3 = [0, 1, 2] := rfl
  have r2 : List.range 2 = [0, 1] := rfl
  have r1 : List.range 1 = [0] := rfl
  simp only [r4, List.flatMap_cons, List.flatMap_nil, Nat.sub_zero, Nat.reduceSub, r3, r2, r1, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, List.append_nil, List.sum_cons, List.sum_nil,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- the (s, i) double sum of `localFm` re-indexed from s ∈ [1, 4] to s + 1, s ∈ [0, 4). -/
private theorem Icc_sum (f : ℕ → ℕ → ℝ) :
    ∑ s ∈ Finset.Icc 1 (5 - 1), ∑ i ∈ Finset.range (5 - s), f s i
      = ∑ s ∈ Finset.range 4, ∑ i ∈ Finset.range (4 - s), f (s + 1) i := by
  rw [show Finset.Icc 1 (5 - 1) = {1, 2, 3, 4} by rfl]
  simp [Finset.sum_range_succ]
  ring

private theorem classData_F (m : Fin 5 → Fin 2) (g : ℕ → ℝ) :
    (classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)).F g
      = localFm (kPsi psiCos16) W5 m (fun l => g l) := by
  have hk : kPsi psiCos16 = kCos := funext kPsi_psiCos16_eq
  rw [hk]
  unfold localFm LIQ.F classData
  simp only []
  congr 1
  · rw [spans_sum, Icc_sum]
    refine Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hs hi
    rw [gapSpan_eq_spanVal g (by omega), mL_getD m (by omega : i < 5), mL_getD m (by omega : i + s + 1 < 5),
      markVal_lt m (by omega : i < 5), markVal_lt m (by omega : i + (s + 1) < 5)]
    have e : (⟨i + (s + 1), (by omega : i + (s + 1) < 5)⟩ : Fin 5) = ⟨i + s + 1, by omega⟩ := by
      ext; simp only; omega
    rw [e]
    show _ = (gam5 (s + 1) i : ℝ) * _ * _ * _
    push_cast
    ring

private theorem classData_claim (m : Fin 5 → Fin 2) :
    (((classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)).claim : ℚ) : ℝ)
      = ∑ i, W5.b i (m i) := by
  have hsum : ∀ f : ℕ → ℚ, ((List.range 5).map f).sum = ∑ i : Fin 5, f i := by
    intro f
    rw [show List.range 5 = [0, 1, 2, 3, 4] from rfl, Fin.sum_univ_five]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, add_assoc]
    rfl
  have hfin : ∀ j : Fin 2, (if (j : ℕ) + 1 = 2 then (1 : Fin 2) else 0) = j := by decide
  unfold classData
  simp only []
  rw [hsum, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.2, mL_getD m i.2, hfin]
  rfl

/-- Node C-bridge-class: one class instance ⟺ the all-marks inequality of `W5` for that pattern
(index translation Fin 4 → ℝ versus ℕ → ℝ; pattern weights; claim). -/
theorem classData_holds_iff (m : Fin 5 → Fin 2) :
    (classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)).Holds ↔
      ∀ g : Fin 4 → ℝ, (∀ l, 0 ≤ g l) → ∑ i, W5.b i (m i) ≤ localFm (kPsi psiCos16) W5 m g := by
  unfold LIQ.Holds
  rw [classData_claim]
  constructor
  · intro h g hg
    have := h (fun l => if hl : l < 4 then g ⟨l, hl⟩ else 0) (fun l => by
      by_cases hl : l < 4
      · simp only [hl, dif_pos]; exact hg _
      · simp only [hl, dif_neg, not_false_eq_true, le_refl])
    rw [classData_F] at this
    convert this using 2
    funext l
    simp [l.2]
  · intro h g hg
    rw [classData_F]
    exact h _ fun l => hg l

/-- Node C-W5-rev: `W5` is reversal-symmetric (hypothesis of L2_2's `localCertAM_of_classes`). -/
theorem W5_revSymm : W5.IsRevSymm := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs i hi
    rw [Finset.mem_Icc] at hs
    rw [Finset.mem_range] at hi
    obtain ⟨h1, h2⟩ := hs
    show (gam5 s i : ℝ) = (gam5 s (5 - s - 1 - i) : ℝ)
    interval_cases s <;> interval_cases i <;> norm_num [gam5]
  · intro l
    show ((mu5.getD l 0 : ℚ) : ℝ) = ((mu5.getD l.rev 0 : ℚ) : ℝ)
    fin_cases l <;> norm_num [mu5]
  · intro i j
    show (b5 i j : ℝ) = (b5 i.rev j : ℝ)
    fin_cases i <;> fin_cases j <;> rfl

/-- Node C-W5-const: the constants of `W5`. -/
theorem W5_consts : W5.a 0 = 1280197 / 10 ^ 8 ∧ W5.a 1 = 48749 / 3125000 ∧ W5.nu = 1 / 125 := by
  have ha0 : ∑ i : Fin 5, b5 i 0 = 1280197 / 10 ^ 8 := by
    rw [Fin.sum_univ_five, show b5 0 0 = 64333 / 25000000 from rfl, show b5 1 0 = 64617 / 25000000 from rfl,
      show b5 2 0 = 248597 / 100000000 from rfl, show b5 3 0 = 64617 / 25000000 from rfl,
      show b5 4 0 = 64333 / 25000000 from rfl]
    norm_num
  have ha1 : ∑ i : Fin 5, b5 i 1 = 48749 / 3125000 := by
    rw [Fin.sum_univ_five, show b5 0 1 = 310701 / 100000000 from rfl, show b5 1 1 = 61913 / 20000000 from rfl,
      show b5 2 1 = 79859 / 25000000 from rfl, show b5 3 1 = 61913 / 20000000 from rfl,
      show b5 4 1 = 310701 / 100000000 from rfl]
    norm_num
  have hnu : ∑ l : Fin (5 - 1), mu5.getD l 0 = 1 / 125 := by
    rw [Fin.sum_univ_four, show mu5.getD ((0 : Fin (5 - 1)) : ℕ) 0 = 3833 / 2500000 from rfl,
      show mu5.getD ((1 : Fin (5 - 1)) : ℕ) 0 = 6167 / 2500000 from rfl,
      show mu5.getD ((2 : Fin (5 - 1)) : ℕ) 0 = 6167 / 2500000 from rfl,
      show mu5.getD ((3 : Fin (5 - 1)) : ℕ) 0 = 3833 / 2500000 from rfl]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · show ∑ i : Fin 5, (b5 i 0 : ℝ) = 1280197 / 10 ^ 8
    rw [← Rat.cast_sum, ha0]
    norm_num
  · show ∑ i : Fin 5, (b5 i 1 : ℝ) = 48749 / 3125000
    rw [← Rat.cast_sum, ha1]
    norm_num
  · show ∑ l : Fin (5 - 1), ((mu5.getD l 0 : ℚ) : ℝ) = 1 / 125
    rw [← Rat.cast_sum, hnu]
    norm_num

/-- every mark pattern or its reversal is one of the 20 canonical classes. -/
theorem classes5_cover (m : Fin 5 → Fin 2) :
    ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1) ∈ classes5 ∨
      ((List.range 5).map fun i => if h : i < 5 then ((m ∘ Fin.rev) ⟨i, h⟩ : ℕ) + 1 else 1) ∈ classes5 := by
  revert m
  decide

/-- the assembly with the certificate theorem (node C21) as an explicit hypothesis. -/
theorem certAM5_of_checks_of_sound (hsound : ∀ C : Cert, C.check = true → C.data.Holds) (C : List Cert)
    (hdata : C.map Cert.data = classes5.map classData) (hchk : ∀ c ∈ C, c.check = true) : CertAM5 := by
  obtain ⟨h0, h1, h2⟩ := W5_consts
  refine ⟨W5, h0, h1, h2, ?_⟩
  refine localCertAM_of_classes W5 (kPsi psiCos16) W5_revSymm
    (fun m => ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1) ∈ classes5)
    classes5_cover ?_
  intro m hm g hg
  have hmem : classData ((List.range 5).map fun i => if h : i < 5 then (m ⟨i, h⟩ : ℕ) + 1 else 1)
      ∈ C.map Cert.data := by
    rw [hdata]
    exact List.mem_map_of_mem hm
  obtain ⟨c, hc, hcd⟩ := List.mem_map.1 hmem
  have hH := hsound c (hchk c hc)
  rw [hcd] at hH
  exact (classData_holds_iff m).1 hH g hg

-- NOT IN THIS MODULE (as above): `certAM5_of_checks` (node C-AM5 / C26), same statement, is proved downstream as
-- `ZetaS.CertV2.ChainV3.certAM5_of_checks` := `certAM5_of_checks_of_sound ChainV3.cert_check_sound` (level A).

end ZetaS.CertV2

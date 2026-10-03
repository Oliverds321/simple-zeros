/-
Track M-cert (L2_2, 28 Sep 2026) — the majorant of lem:sigd-env, ANALYTIC PART, and the reduction of `CertMajV2` to three
explicitly stated nodes.

The majorant (round2/d7_6_numerics/r4_majorant_arb.py, "B′"): with h = 1/60,
  B(s) = h · sinc(πhs)² · P(s),   P(s) = β₀ + 2 Σ_{j=1}^{59} β_j cos(2πjhs) = β₀ + 2 Σ β_j cos(π(js/30)),
β_j = the 60 binary64 numbers of round2/d6_6b_numerics/majorant_delta1_beta.npy, taken EXACTLY:
  * file sha256 = fd909f79669e2fc1ba5fd4e44d01d6007ccf5303b7ce62d4c5ee08f7ef024845 (checked 28 Sep 2026, = the architect's);
  * conversion: numpy float64 → Python `fractions.Fraction(float(x))` (exact dyadic n/2^k), printed as `n / d : ℚ`
    (the conversion one-liner is in reports/L2_2c_nodes.md; py/mcert_cells.py re-checks the sha256).
Its Fourier transform is the piecewise-linear interpolation of the β_j at the nodes j/60:
  B̂(t) = ∫ B(s) cos(2πts) ds = β₀Λ(60t) + Σ_{j=1}^{59} β_j (Λ(60t − j) + Λ(60t + j)),   Λ(u) = (1 − |u|)₊.

Nodes of this file:
  * `FP` (Fourier pair, stated as a `Prop`): ∫_ℝ sinc(πu)² cos(2πωu) du = Λ(ω) for all ω.  PROVED in
    FP_FourierPair.lean (`MCert.fp_holds`, level A: Mathlib's Fourier inversion `Continuous.fourierInv_fourier_eq`
    for the continuous integrable Λ, whose transform sinc(π·)² is computed on [−1, 1] by elementary antiderivatives).
  * `NPos`  (numerical, cell certificate): P(s) ≥ 0 for s ∈ [0, 30].
  * `NMaj`  (numerical, cell certificate): cos(8s/5) / ((5/4) sin(4/5)) ≤ B(s) for s ∈ [0, 1/2].
Proved here (level A): B even, integrable; B̂ = the piecewise-linear interpolant (from FP); B̂ = 0 on |t| ≥ 1; ∫B = β₀;
|B̂| ≤ |β₅₂| on [3/4, 1]; 2β₀ + 4|β₅₂| < 33/10 (exact rationals); P ≥ 0 on ℝ from NPos (even, 60-periodic);
∫_{−1/2}^{1/2} cos(8s/5) ds = (5/4) sin(4/5); and `certMajV2_of_nodes : FP → NPos → NMaj → CertMajV2` (file CertMajV2.lean).
-/
import ZetaS.Interfaces

open Real MeasureTheory Set Finset

noncomputable section

namespace ZetaS

namespace MCert

/-- the 60 coefficients `β_j` (exact binary64 values), `β_j = 0` for `j ≥ 60`. -/
def betaQ : ℕ → ℚ
  | 0 => (1751508895300479 / 1125899906842624 : ℚ)
  | 1 => (871124775481349 / 562949953421312 : ℚ)
  | 2 => (6921101277396945 / 4503599627370496 : ℚ)
  | 3 => (3427331428338137 / 2251799813685248 : ℚ)
  | 4 => (1692871448062129 / 1125899906842624 : ℚ)
  | 5 => (6672840738565849 / 4503599627370496 : ℚ)
  | 6 => (3279131269623991 / 2251799813685248 : ℚ)
  | 7 => (1607373656513523 / 1125899906842624 : ℚ)
  | 8 => (3143923769222297 / 2251799813685248 : ℚ)
  | 9 => (383359965783167 / 281474976710656 : ℚ)
  | 10 => (5968411471291657 / 4503599627370496 : ℚ)
  | 11 => (5792835919318019 / 4503599627370496 : ℚ)
  | 12 => (2803926457070077 / 2251799813685248 : ℚ)
  | 13 => (5414794718899799 / 4503599627370496 : ℚ)
  | 14 => (2607354153664311 / 2251799813685248 : ℚ)
  | 15 => (2504254386083749 / 2251799813685248 : ℚ)
  | 16 => (2398493186406135 / 2251799813685248 : ℚ)
  | 17 => (2290807676627735 / 2251799813685248 : ℚ)
  | 18 => (545387957081061 / 562949953421312 : ℚ)
  | 19 => (2071286451299159 / 2251799813685248 : ℚ)
  | 20 => (1960507963684143 / 2251799813685248 : ℚ)
  | 21 => (7398456317502415 / 9007199254740992 : ℚ)
  | 22 => (6955916582993395 / 9007199254740992 : ℚ)
  | 23 => (6517531865552225 / 9007199254740992 : ℚ)
  | 24 => (6083290160686403 / 9007199254740992 : ℚ)
  | 25 => (5656267474935337 / 9007199254740992 : ℚ)
  | 26 => (5236756797117351 / 9007199254740992 : ℚ)
  | 27 => (4826979180497057 / 9007199254740992 : ℚ)
  | 28 => (8855987078147197 / 18014398509481984 : ℚ)
  | 29 => (1010319772025981 / 2251799813685248 : ℚ)
  | 30 => (7335918475097197 / 18014398509481984 : ℚ)
  | 31 => (1654239350527385 / 4503599627370496 : ℚ)
  | 32 => (5929388775947697 / 18014398509481984 : ℚ)
  | 33 => (2636900839732333 / 9007199254740992 : ℚ)
  | 34 => (4651796656585545 / 18014398509481984 : ℚ)
  | 35 => (8131659503433883 / 36028797018963968 : ℚ)
  | 36 => (878533511303857 / 4503599627370496 : ℚ)
  | 37 => (6001196005079605 / 36028797018963968 : ℚ)
  | 38 => (5046987331530743 / 36028797018963968 : ℚ)
  | 39 => (4170503753546983 / 36028797018963968 : ℚ)
  | 40 => (6735783837229385 / 72057594037927936 : ℚ)
  | 41 => (330189442431723 / 4503599627370496 : ℚ)
  | 42 => (1989128566757009 / 36028797018963968 : ℚ)
  | 43 => (1410787423646803 / 36028797018963968 : ℚ)
  | 44 => (3621974192671095 / 144115188075855872 : ℚ)
  | 45 => (3763216780774981 / 288230376151711744 : ℚ)
  | 46 => (3244331135236463 / 1152921504606846976 : ℚ)
  | 47 => (-3212389659911473 / 576460752303423488 : ℚ)
  | 48 => (-7068595394965989 / 576460752303423488 : ℚ)
  | 49 => (-4985464416986187 / 288230376151711744 : ℚ)
  | 50 => (-2995459692986379 / 144115188075855872 : ℚ)
  | 51 => (-206523044511113 / 9007199254740992 : ℚ)
  | 52 => (-3424864291128123 / 144115188075855872 : ℚ)
  | 53 => (-6744005639923137 / 288230376151711744 : ℚ)
  | 54 => (-24779131403579 / 1125899906842624 : ℚ)
  | 55 => (-2840112757107789 / 144115188075855872 : ℚ)
  | 56 => (-4812871826937449 / 288230376151711744 : ℚ)
  | 57 => (-3793418858028979 / 288230376151711744 : ℚ)
  | 58 => (-2598855283662429 / 288230376151711744 : ℚ)
  | 59 => (-5309413051505067 / 1152921504606846976 : ℚ)
  | _ => 0

/-- `β_j` as a real number. -/
def beta (j : ℕ) : ℝ := (betaQ j : ℝ)

/-- the trigonometric polynomial `P(s) = β₀ + 2 Σ_{j=1}^{59} β_j cos(π j s/30)`. -/
def Pmaj (s : ℝ) : ℝ := beta 0 + 2 * ∑ j ∈ Icc 1 59, beta j * Real.cos (π * (j * s / 30))

/-- the majorant `B(s) = (1/60) sinc(πs/60)² P(s)`. -/
def Bmaj (s : ℝ) : ℝ := 1 / 60 * Real.sinc (π * s / 60) ^ 2 * Pmaj s

/-- the unit hat `Λ(u) = (1 − |u|)₊`. -/
def tri (u : ℝ) : ℝ := max (1 - |u|) 0

/-- the piecewise-linear interpolant `B̂(t) = β₀Λ(60t) + Σ_{j=1}^{59} β_j (Λ(60t − j) + Λ(60t + j))`. -/
def BhatPL (t : ℝ) : ℝ := beta 0 * tri (60 * t) + ∑ j ∈ Icc 1 59, beta j * (tri (60 * t - j) + tri (60 * t + j))

/-- **FP** — the Fourier pair sinc² ↔ triangle (classical; not proved here). -/
def FP : Prop := ∀ ω : ℝ, ∫ u, Real.sinc (π * u) ^ 2 * Real.cos (2 * π * ω * u) = tri ω

/-- **NPos** — numerical node (cell certificate on [0, 30]). -/
def NPos : Prop := ∀ s ∈ Icc (0 : ℝ) 30, 0 ≤ Pmaj s

/-- **NMaj** — numerical node (cell certificate on [0, 1/2]); `(5/4) sin(4/5) = ∫_{−1/2}^{1/2} cos(8s/5) ds`. -/
def NMaj : Prop := ∀ s ∈ Icc (0 : ℝ) (1 / 2), Real.cos (8 / 5 * s) / (5 / 4 * Real.sin (4 / 5)) ≤ Bmaj s

/-! ### elementary facts -/

lemma tri_nonneg (u : ℝ) : 0 ≤ tri u := le_max_right _ _

lemma tri_eq_zero {u : ℝ} (hu : 1 ≤ |u|) : tri u = 0 := by
  unfold tri; exact max_eq_right (by linarith)

lemma tri_le_one (u : ℝ) : tri u ≤ 1 := by
  unfold tri; exact max_le (by linarith [abs_nonneg u]) zero_le_one

lemma Pmaj_neg (s : ℝ) : Pmaj (-s) = Pmaj s := by
  unfold Pmaj
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show π * (j * -s / 30) = -(π * (j * s / 30)) by ring, Real.cos_neg]

lemma Pmaj_periodic (s : ℝ) (k : ℤ) : Pmaj (s + 60 * k) = Pmaj s := by
  unfold Pmaj
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  have : π * (j * (s + 60 * k) / 30) = π * (j * s / 30) + ((j : ℤ) * k : ℤ) * (2 * π) := by
    push_cast; ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma Bmaj_neg (s : ℝ) : Bmaj (-s) = Bmaj s := by
  unfold Bmaj
  rw [Pmaj_neg, show π * -s / 60 = -(π * s / 60) by ring, Real.sinc_neg]

/-- `P ≥ 0` on ℝ from `P ≥ 0` on `[0, 30]` (P even and 60-periodic). -/
lemma Pmaj_nonneg (h : NPos) (s : ℝ) : 0 ≤ Pmaj s := by
  set k : ℤ := ⌊(s + 30) / 60⌋ with hk
  set s' := s - 60 * k with hs'
  have h1 : (k : ℝ) ≤ (s + 30) / 60 := Int.floor_le _
  have h2 : (s + 30) / 60 < k + 1 := Int.lt_floor_add_one _
  have hper : Pmaj s = Pmaj s' := by
    have := Pmaj_periodic s' k
    rw [hs', sub_add_cancel] at this
    exact this
  rw [hper]
  rcases le_total 0 s' with hpos | hneg
  · exact h s' ⟨hpos, by rw [hs']; linarith⟩
  · rw [← Pmaj_neg]; exact h (-s') ⟨by linarith, by rw [hs']; linarith⟩

lemma sinc_sq_le (x : ℝ) : Real.sinc x ^ 2 ≤ 2 / (1 + x ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt (x ^ 2) 1 with hx | hx
  · have h1 := Real.abs_sinc_le_one x
    have : Real.sinc x ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
    nlinarith [sq_nonneg (Real.sinc x)]
  · have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
    rw [Real.sinc_of_ne_zero hx0, div_pow]
    have hs : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
    have hx2 : 0 < x ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hx2]
    nlinarith

lemma sinc_scaled_sq_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.sinc (c * s) ^ 2) := by
  have hint : Integrable (fun s : ℝ => (2 / min 1 (c ^ 2)) * (1 + s ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  refine hint.mono' ?_ ?_
  · exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2 |>.aestronglyMeasurable
  · refine ae_of_all _ fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hm : 0 < min 1 (c ^ 2) := lt_min one_pos (by positivity)
    have h1 : min 1 (c ^ 2) ≤ 1 := min_le_left _ _
    have h2 : min 1 (c ^ 2) ≤ c ^ 2 := min_le_right _ _
    calc Real.sinc (c * s) ^ 2 ≤ 2 / (1 + (c * s) ^ 2) := sinc_sq_le _
      _ ≤ 2 / (min 1 (c ^ 2) * (1 + s ^ 2)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        nlinarith [sq_nonneg s, mul_le_mul_of_nonneg_right h2 (sq_nonneg s)]
      _ = 2 / min 1 (c ^ 2) * (1 + s ^ 2)⁻¹ := by
        rw [div_mul_eq_div_div, div_eq_mul_inv (2 / min 1 (c ^ 2))]

lemma Pmaj_bound (s : ℝ) : |Pmaj s| ≤ |beta 0| + 2 * ∑ j ∈ Icc 1 59, |beta j| := by
  unfold Pmaj
  calc |beta 0 + 2 * ∑ j ∈ Icc 1 59, beta j * Real.cos (π * (j * s / 30))|
      ≤ |beta 0| + |2 * ∑ j ∈ Icc 1 59, beta j * Real.cos (π * (j * s / 30))| := abs_add_le _ _
    _ ≤ |beta 0| + 2 * ∑ j ∈ Icc 1 59, |beta j| := by
        rw [abs_mul, abs_two]
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

lemma Pmaj_continuous : Continuous Pmaj := by
  unfold Pmaj; fun_prop

lemma Bmaj_integrable : Integrable Bmaj := by
  have h := (sinc_scaled_sq_integrable (π / 60) (by positivity)).const_mul (1 / 60)
  have e : (fun s => 1 / 60 * Real.sinc (π / 60 * s) ^ 2) = fun s => 1 / 60 * Real.sinc (π * s / 60) ^ 2 := by
    funext s; ring_nf
  rw [e] at h
  exact h.mul_bdd Pmaj_continuous.aestronglyMeasurable (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs]; exact Pmaj_bound s)

/-! ### the transform, from FP -/

/-- the scaled pair: `∫ (1/60) sinc(πs/60)² cos(2πτs) ds = Λ(60τ)`. -/
lemma scaled_pair (hFP : FP) (τ : ℝ) :
    ∫ s, 1 / 60 * Real.sinc (π * s / 60) ^ 2 * Real.cos (2 * π * τ * s) = tri (60 * τ) := by
  have h := MeasureTheory.Measure.integral_comp_mul_left
    (fun y : ℝ => 1 / 60 * Real.sinc (π * y / 60) ^ 2 * Real.cos (2 * π * τ * y)) (60 : ℝ)
  have e : (fun x : ℝ => 1 / 60 * Real.sinc (π * (60 * x) / 60) ^ 2 * Real.cos (2 * π * τ * (60 * x)))
      = fun x => 1 / 60 * (Real.sinc (π * x) ^ 2 * Real.cos (2 * π * (60 * τ) * x)) := by
    funext x
    rw [show π * (60 * x) / 60 = π * x by ring, show 2 * π * τ * (60 * x) = 2 * π * (60 * τ) * x by ring]
    ring
  rw [e, integral_const_mul, hFP (60 * τ)] at h
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 60⁻¹), smul_eq_mul] at h
  linarith

lemma h_integrable (τ : ℝ) :
    Integrable (fun s => 1 / 60 * Real.sinc (π * s / 60) ^ 2 * Real.cos (2 * π * τ * s)) := by
  have h := (sinc_scaled_sq_integrable (π / 60) (by positivity)).const_mul (1 / 60)
  have e : (fun s => 1 / 60 * Real.sinc (π / 60 * s) ^ 2) = fun s => 1 / 60 * Real.sinc (π * s / 60) ^ 2 := by
    funext s; ring_nf
  rw [e] at h
  exact h.mul_bdd (by fun_prop : Continuous fun s => Real.cos (2 * π * τ * s)).aestronglyMeasurable
    (ae_of_all _ fun s => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- **the transform of B** is the piecewise-linear interpolant (from FP). -/
theorem Bmaj_transform (hFP : FP) (t : ℝ) :
    ∫ s, Bmaj s * Real.cos (2 * π * t * s) = BhatPL t := by
  set hf : ℝ → ℝ → ℝ := fun τ s => 1 / 60 * Real.sinc (π * s / 60) ^ 2 * Real.cos (2 * π * τ * s) with hhf
  have hc : ∀ j : ℕ, ∀ s : ℝ, Real.cos (2 * π * (t - j / 60) * s) + Real.cos (2 * π * (t + j / 60) * s)
      = 2 * Real.cos (π * (j * s / 30)) * Real.cos (2 * π * t * s) := by
    intro j s
    rw [show 2 * π * (t - j / 60) * s = 2 * π * t * s - π * (j * s / 30) by ring,
      show 2 * π * (t + j / 60) * s = 2 * π * t * s + π * (j * s / 30) by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hpt : (fun s => Bmaj s * Real.cos (2 * π * t * s))
      = fun s => beta 0 * hf t s + ∑ j ∈ Icc 1 59, beta j * (hf (t - j / 60) s + hf (t + j / 60) s) := by
    funext s
    simp only [hhf, Bmaj, Pmaj]
    have e : ∀ j ∈ Finset.Icc 1 59, beta j * (1 / 60 * Real.sinc (π * s / 60) ^ 2 * Real.cos (2 * π * (t - j / 60) * s)
        + 1 / 60 * Real.sinc (π * s / 60) ^ 2 * Real.cos (2 * π * (t + j / 60) * s))
        = 1 / 60 * Real.sinc (π * s / 60) ^ 2 * Real.cos (2 * π * t * s)
          * (2 * (beta j * Real.cos (π * (j * s / 30)))) := by
      intro j _
      rw [← mul_add, hc j s]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hi0 : Integrable (fun s => beta 0 * hf t s) := (h_integrable t).const_mul _
  have hij : ∀ j : ℕ, Integrable (fun s => beta j * (hf (t - j / 60) s + hf (t + j / 60) s)) := fun j =>
    ((h_integrable _).add (h_integrable _)).const_mul _
  have hi1 : Integrable (fun s => ∑ j ∈ Icc 1 59, beta j * (hf (t - j / 60) s + hf (t + j / 60) s)) :=
    integrable_finsetSum _ fun j _ => hij j
  rw [hpt, integral_add hi0 hi1, integral_const_mul, integral_finsetSum _ fun j _ => hij j]
  unfold BhatPL
  congr 1
  · simp only [hhf]; rw [scaled_pair hFP]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_add (h_integrable _) (h_integrable _)]
    try simp only [hhf]
    rw [scaled_pair hFP, scaled_pair hFP]
    congr 2 <;> ring_nf

/-! ### properties of the interpolant -/

lemma BhatPL_zero_of_one_le {t : ℝ} (ht : 1 ≤ |t|) : BhatPL t = 0 := by
  unfold BhatPL
  have h0 : tri (60 * t) = 0 := tri_eq_zero (by rw [abs_mul]; norm_num; linarith)
  rw [h0, mul_zero, zero_add]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' := Finset.mem_Icc.1 hj
  have hjr : (j : ℝ) ≤ 59 := by exact_mod_cast hj'.2
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj'.1
  rcases le_or_gt 0 t with htp | htn
  · rw [abs_of_nonneg htp] at ht
    rw [tri_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith),
      tri_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)]; ring
  · rw [abs_of_neg htn] at ht
    rw [tri_eq_zero (by rw [abs_of_neg (by linarith)]; linarith),
      tri_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)]; ring

lemma BhatPL_at_zero : BhatPL 0 = beta 0 := by
  unfold BhatPL
  have h0 : tri (60 * 0) = 1 := by unfold tri; norm_num
  rw [h0, mul_one]
  have : ∑ j ∈ Icc 1 59, beta j * (tri (60 * 0 - j) + tri (60 * 0 + j)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    rw [tri_eq_zero (by rw [abs_of_neg (by linarith)]; linarith),
      tri_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)]; ring
  rw [this, add_zero]

/-- the node values beyond 44 are bounded by `|β₅₂|`. -/
lemma beta_le_b52 (j : ℕ) (hj : 45 ≤ j) : |beta j| ≤ |beta 52| := by
  unfold beta
  rcases Nat.lt_or_ge j 60 with h | h
  · interval_cases j <;> simp only [betaQ] <;> norm_num [abs_div]
  · have : betaQ j = 0 := by
      unfold betaQ
      split <;> first | omega | rfl
    rw [this]; simp

/-- on `[3/4, 1]`, `|B̂| ≤ |β₅₂|` (linear interpolation between consecutive nodes 45, …, 60). -/
lemma BhatPL_bound {t : ℝ} (ht : t ∈ Icc (3 / 4 : ℝ) 1) : |BhatPL t| ≤ |beta 52| := by
  obtain ⟨ht1, ht2⟩ := ht
  set u := 60 * t with hu
  have hu1 : 45 ≤ u := by rw [hu]; linarith
  have hu2 : u ≤ 60 := by rw [hu]; linarith
  set k : ℕ := ⌊u⌋₊ with hk
  have hk1 : (k : ℝ) ≤ u := Nat.floor_le (by linarith)
  have hk2 : u < k + 1 := Nat.lt_floor_add_one u
  have hk45 : 45 ≤ k := Nat.le_floor (by norm_num; linarith)
  have hk60 : k ≤ 60 := by
    have : (k : ℝ) ≤ 60 := le_trans hk1 hu2
    exact_mod_cast this
  unfold BhatPL
  rw [← hu]
  have h0 : tri u = 0 := tri_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [h0, mul_zero, zero_add]
  -- only j = k, k+1 contribute
  have hterm : ∀ j ∈ Finset.Icc 1 59, beta j * (tri (u - j) + tri (u + j))
      = (if j = k then beta j * (1 - (u - k)) else 0) + (if j = k + 1 then beta j * (u - k) else 0) := by
    intro j hj
    have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    have hplus : tri (u + j) = 0 := tri_eq_zero (by rw [abs_of_pos (by linarith)]; linarith)
    rw [hplus, add_zero]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, if_neg (by omega)]
      unfold tri
      rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]; ring
    · by_cases hjk1 : j = k + 1
      · subst hjk1
        rw [if_neg (by omega), if_pos rfl]
        unfold tri
        push_cast
        rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]; ring
      · rw [if_neg hjk, if_neg hjk1]
        rcases Nat.lt_or_gt_of_ne hjk with hlt | hgt
        · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
          rw [tri_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith)]; ring
        · have : (k : ℝ) + 2 ≤ j := by
            have : k + 2 ≤ j := by omega
            exact_mod_cast this
          rw [tri_eq_zero (by rw [abs_of_nonpos (by linarith)]; linarith)]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  have hθ0 : 0 ≤ u - k := by linarith
  have hθ1 : u - k ≤ 1 := by linarith
  have hb1 : |beta k| ≤ |beta 52| := beta_le_b52 k hk45
  have hb2 : |beta (k + 1)| ≤ |beta 52| := beta_le_b52 (k + 1) (by omega)
  have e1 : |(if k ∈ Finset.Icc 1 59 then beta k * (1 - (u - k)) else 0)| ≤ |beta 52| * (1 - (u - k)) := by
    split_ifs
    · rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 - (u - k) by linarith)]
      exact mul_le_mul_of_nonneg_right hb1 (show (0 : ℝ) ≤ 1 - (u - k) by linarith)
    · simp only [abs_zero]; exact mul_nonneg (abs_nonneg _) (show (0 : ℝ) ≤ 1 - (u - k) by linarith)
  have e2 : |(if k + 1 ∈ Finset.Icc 1 59 then beta (k + 1) * (u - k) else 0)| ≤ |beta 52| * (u - k) := by
    split_ifs
    · rw [abs_mul, abs_of_nonneg hθ0]
      exact mul_le_mul_of_nonneg_right hb2 hθ0
    · simp only [abs_zero]; exact mul_nonneg (abs_nonneg _) hθ0
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ |beta 52| * (1 - (u - k)) + |beta 52| * (u - k) := add_le_add e1 e2
    _ = |beta 52| := by ring

lemma final_rational : 2 * beta 0 + 4 * |beta 52| < 33 / 10 := by
  unfold beta
  simp only [betaQ]
  norm_num [abs_div]

/-- `∫_{−1/2}^{1/2} cos(8s/5) ds = (5/4) sin(4/5)`. -/
lemma integral_psiCos16 : ∫ t in (-(1 / 2 : ℝ))..(1 / 2), psiCos16 t = 5 / 4 * Real.sin (4 / 5) := by
  unfold psiCos16
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) (by norm_num : (8 / 5 : ℝ) ≠ 0),
    integral_cos]
  rw [show (8 / 5 : ℝ) * (1 / 2) = 4 / 5 by norm_num, show (8 / 5 : ℝ) * -(1 / 2) = -(4 / 5) by norm_num,
    Real.sin_neg, smul_eq_mul]
  ring

end MCert

end ZetaS

end

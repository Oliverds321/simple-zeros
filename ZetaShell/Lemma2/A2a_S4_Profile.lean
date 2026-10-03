/-
A2a_S4_Profile (L7_8, round 2): **Step 4 of the proof of Lemma 2(a)** (sec_shell.tex l.343–347): the change of
variables `q = |j|/(r|β|)` turns the main term into the profile integral. (L7_8: open; L7_11: proved, see below.)

`|mainSum − ∫_{η−δ/2}^{η+δ/2} Q² g_r(rQ|β|) dβ| ≤ C δ (1 + log Q)` for `1 ≤ r ≤ Q`, `|η| ≤ 1/r`, `0 < δ < 1`.
The draft says "exactly"; it is exact when the window lies in `|β| ≤ 1/r` (every line point has `q ≥ 1`). Otherwise
the profile also counts lines `j < r|β|`, whose points would have `q < 1`; they contribute
`≤ Q²∫ v⁻² Σ_{j<r|β|} φ(j) Σ_{e≤v}|c_e| dβ ≪ δ(1 + log Q)` (`|𝔈| ≤ 1`, `v = rQ|β|`). Relative to `δQ²` this is
`≤ t₃` of the bracket.

L7_11 (28 Sep 2026, round 2): PROVED, statement unchanged. Route: per line, `lineInt_changeVar` (L711_S4a_ChangeVar)
and its reflection for `j < 0` turn `mainSum` into `∫ T(|β|)`, `T(t) = Σ_{k≤M} (φ(k)/k)(1/r) Σ_{e≤Q} c_e 𝔈 Λ_{k,e}(t)`;
pointwise, `T(t)` and `Q² g_r(rQt)` agree term by term except for the lines `kQ < v = rQt` (points `q < 1`), which
cost at most `B_E Σ_{e≤v}|c_e| ≤ B_E C (1 + log v)` (`|𝔈| ≤ B_E = e^{2ζ(2)} + 1`; `Σ_{e≤v}|μ(e)|/φ(e)` from the shared
`L711_MuSqPhi`); `v ≤ Q²`.
-/
import ZetaShell.Lemma2.A2a_StepDefs
import ZetaShell.Lemma2.A2a_S5_Window
import ZetaShell.Lemma2.L711_S4a_ChangeVar
import ZetaShell.Lemma2.L711_MuSqPhi

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace ZetaShell
namespace TrackF

/-! ### L7_11: auxiliary lemmas for `step4_profile` -/

theorem w_eq_zero_gt1 (F : Fam) {x : ℝ} (hx : 1 < x) : F.w x = 0 := by
  cases F <;> simp only [Fam.w] <;> rw [if_neg (by intro h; linarith [h.2])]

theorem abs_w_le_one (F : Fam) (x : ℝ) : |F.w x| ≤ 1 := by
  cases F <;> simp only [Fam.w] <;> split_ifs with h
  all_goals first
    | (rw [abs_one])
    | (rw [abs_zero]; norm_num)
    | (rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [h.1, h.2])

/-- the constant bounding `|𝔈|`. -/
def BE : ℝ := Real.exp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) + 1

theorem inv_one_sub_le_exp {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have h1 : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith
  have h2 := Real.add_one_le_exp (2 * x)
  linarith

theorem prod_inv_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ Real.exp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := by
  have hz : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.mpr one_lt_two
  calc ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2)⁻¹ ≤ ∏ p ∈ S, Real.exp (2 * (1 / (p : ℝ) ^ 2)) := by
        apply Finset.prod_le_prod
        · intro p hp
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
          have : 1 / (p : ℝ) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
          exact inv_nonneg.mpr (by linarith)
        · intro p hp
          have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).two_le
          apply inv_one_sub_le_exp (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    _ = Real.exp (2 * ∑ p ∈ S, 1 / (p : ℝ) ^ 2) := by
        rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ Real.exp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        have := hz.sum_le_tsum S (fun i _ => by positivity)
        linarith

theorem abs_Ecoef_le (k : FKind) (r j e : ℕ) : |Ecoef k r j e| ≤ BE := by
  have hBE1 : 1 ≤ BE := by unfold BE; have := Real.exp_pos (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2); linarith
  have hB : |∏ p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j), (1 - 1 / (p : ℝ))| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun p _ => abs_nonneg _)
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have : 0 < 1 / (p : ℝ) := by positivity
    rw [abs_of_nonneg (by linarith)]; linarith
  have hC : |∏ p ∈ (Nat.gcd r j).primeFactors, hE k e p| ≤ 1 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun p _ => abs_nonneg _)
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have : 0 < 1 / (p : ℝ) := by positivity
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    cases k <;> simp only [hE] <;> split_ifs <;> first | (rw [abs_zero]; norm_num) | (rw [abs_one]) |
      (rw [abs_of_nonneg (by linarith)]; linarith)
  have hA : ∀ A : ℝ, |A| ≤ BE →
      |A * (∏ p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j), (1 - 1 / (p : ℝ)))
        * ∏ p ∈ (Nat.gcd r j).primeFactors, hE k e p| ≤ BE := by
    intro A hA'
    rw [abs_mul, abs_mul]
    calc _ ≤ BE * 1 * 1 :=
          mul_le_mul (mul_le_mul hA' hB (abs_nonneg _) (by linarith)) hC (abs_nonneg _) (by linarith)
      _ = BE := by ring
  cases k
  · apply hA
    have hP := prod_inv_le_exp (r * j * e).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    have hP0 : 0 ≤ ∏ p ∈ (r * j * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
      apply Finset.prod_nonneg
      intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      have : 1 / (p : ℝ) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
      exact inv_nonneg.mpr (by linarith)
    have hpi : (6 : ℝ) / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
    rw [abs_of_nonneg (by positivity)]
    unfold BE
    calc 6 / Real.pi ^ 2 * ∏ p ∈ (r * j * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹
        ≤ 1 * Real.exp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := mul_le_mul hpi hP hP0 (by norm_num)
      _ ≤ _ := by linarith
  · apply hA
    rw [abs_one]; exact hBE1

/-- the transformed line integrand `Λ_{k,e}(t)`. -/
def Lam (F : Fam) (Q r k e : ℕ) (t : ℝ) : ℝ :=
  Set.indicator (Set.Icc ((k : ℝ) / (r * Q)) ((k : ℝ) / r))
    (fun β => (k : ℝ) / (r * β ^ 2) * F.w ((k : ℝ) / (r * β) * e / Q)) t

theorem Lam_measurable (F : Fam) (Q r k e : ℕ) : Measurable (Lam F Q r k e) := by
  unfold Lam
  apply Measurable.indicator _ measurableSet_Icc
  refine Measurable.mul (measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))) ?_
  exact F.measurable_w.comp (((measurable_const.div (measurable_const.mul measurable_id)).mul_const _).div_const _)

theorem abs_Lam_le (F : Fam) (Q r k e : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hk : 1 ≤ k) (t : ℝ) :
    |Lam F Q r k e t| ≤ r * Q ^ 2 := by
  unfold Lam
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  by_cases ht : t ∈ Set.Icc ((k : ℝ) / (r * Q)) ((k : ℝ) / r)
  · rw [Set.indicator_of_mem ht, abs_mul]
    have ht0 : (k : ℝ) / (r * Q) ≤ t := ht.1
    have hpos : 0 < (k : ℝ) / (r * Q) := by positivity
    have htpos : 0 < t := lt_of_lt_of_le hpos ht0
    have hw := abs_w_le_one F ((k : ℝ) / (r * t) * e / Q)
    have h1 : |(k : ℝ) / (r * t ^ 2)| ≤ r * Q ^ 2 := by
      rw [abs_of_pos (by positivity), div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at ht0
      -- k ≤ r Q t, so k ≤ k² ≤ (rQt)² and k·... : k ≤ r Q² · r t² ⇐ k ≤ (rQt)² / k·...
      have h3 : (k : ℝ) ≤ (r * Q * t) ^ 2 := by nlinarith
      nlinarith
    calc |(k : ℝ) / (r * t ^ 2)| * |F.w ((k : ℝ) / (r * t) * e / Q)| ≤ (r * Q ^ 2) * 1 :=
          mul_le_mul h1 hw (abs_nonneg _) (by positivity)
      _ = r * Q ^ 2 := by ring
  · rw [Set.indicator_of_notMem ht, abs_zero]; positivity

theorem intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (K : ℝ) (hK : ∀ x, |f x| ≤ K) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  IntervalIntegrable.mono_fun' (g := fun _ => K) intervalIntegrable_const hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by show ‖f x‖ ≤ K; rw [Real.norm_eq_abs]; exact hK x))

/-- positive lines. -/
theorem lineInt_pos (F : Fam) (Q r k e : ℕ) (η δ : ℝ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hk : 1 ≤ k) (hδ : 0 < δ) :
    lineInt F Q r (k : ℤ) e η δ = ∫ β in (η - δ / 2)..(η + δ / 2), Lam F Q r k e β := by
  rw [lineInt_changeVar F Q r (k : ℤ) e η δ hQ hr (by exact_mod_cast hk) hδ]
  simp only [Int.cast_natCast]
  rfl

/-- negative lines, by reflection. -/
theorem lineInt_neg (F : Fam) (Q r k e : ℕ) (η δ : ℝ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hk : 1 ≤ k) (hδ : 0 < δ) :
    lineInt F Q r (-(k : ℤ)) e η δ = ∫ β in (η - δ / 2)..(η + δ / 2), Lam F Q r k e (-β) := by
  have hrefl : lineInt F Q r (-(k : ℤ)) e η δ = lineInt F Q r (k : ℤ) e (-η) δ := by
    unfold lineInt
    have hS : {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ η - δ / 2 ≤ (((-(k : ℤ)) : ℤ) : ℝ) / (q * r) ∧
          (((-(k : ℤ)) : ℤ) : ℝ) / (q * r) ≤ η + δ / 2}
        = {q : ℝ | 1 ≤ q ∧ q ≤ Q ∧ -η - δ / 2 ≤ (((k : ℤ)) : ℝ) / (q * r) ∧
          (((k : ℤ)) : ℝ) / (q * r) ≤ -η + δ / 2} := by
      ext q
      simp only [Set.mem_setOf_eq, Int.cast_neg, Int.cast_natCast, neg_div]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, by linarith, by linarith⟩
      · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, by linarith, by linarith⟩
    rw [hS]
  rw [hrefl, lineInt_pos F Q r k e (-η) δ hQ hr hk hδ,
    intervalIntegral.integral_comp_neg (a := η - δ / 2) (b := η + δ / 2) (Lam F Q r k e)]
  congr 1 <;> ring

/-- `Λ(β) + Λ(−β) = Λ(|β|)`. -/
theorem Lam_add_neg (F : Fam) (Q r k e : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hk : 1 ≤ k) (β : ℝ) :
    Lam F Q r k e β + Lam F Q r k e (-β) = Lam F Q r k e |β| := by
  have hpos : 0 < (k : ℝ) / (r * Q) := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    positivity
  have hnot : ∀ x : ℝ, x ≤ 0 → Lam F Q r k e x = 0 := by
    intro x hx
    unfold Lam
    rw [Set.indicator_of_notMem]
    intro h; linarith [h.1]
  rcases le_or_gt 0 β with h | h
  · rcases h.lt_or_eq with h' | h'
    · rw [abs_of_pos h', hnot (-β) (by linarith), add_zero]
    · subst h'; simp [hnot 0 le_rfl]
  · rw [abs_of_neg h, hnot β h.le, zero_add]

/-- sums over the nonzero lines `0 < |j| ≤ M`. -/
theorem sum_lines (M : ℕ) (f : ℤ → ℝ) :
    ∑ j ∈ (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun j => j ≠ 0), f j
      = ∑ k ∈ Finset.Icc 1 M, (f (k : ℤ) + f (-(k : ℤ))) := by
  rw [Finset.sum_add_distrib]
  have hinj1 : Set.InjOn (fun k : ℕ => (k : ℤ)) (Finset.Icc 1 M : Set ℕ) := by
    intro x _ y _ h
    have h' : (x : ℤ) = (y : ℤ) := h
    exact_mod_cast h'
  have hinj2 : Set.InjOn (fun k : ℕ => -(k : ℤ)) (Finset.Icc 1 M : Set ℕ) := by
    intro x _ y _ h
    have h' : -(x : ℤ) = -(y : ℤ) := h
    rw [neg_inj] at h'
    exact_mod_cast h'
  rw [← Finset.sum_image (f := f) (g := fun k : ℕ => (k : ℤ)) (fun x hx y hy h => hinj1 hx hy h),
    ← Finset.sum_image (f := f) (g := fun k : ℕ => -(k : ℤ)) (fun x hx y hy h => hinj2 hx hy h)]
  rw [← Finset.sum_union]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
      · left; exact ⟨n, ⟨by omega, by omega⟩, rfl⟩
      · right; exact ⟨n, ⟨by omega, by omega⟩, rfl⟩
    · rintro (⟨n, ⟨h1, h2⟩, rfl⟩ | ⟨n, ⟨h1, h2⟩, rfl⟩)
      · exact ⟨⟨by omega, by omega⟩, by omega⟩
      · exact ⟨⟨by omega, by omega⟩, by omega⟩
  · rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [Finset.mem_image, Finset.mem_Icc] at hj1 hj2
    obtain ⟨n, ⟨h1, _⟩, rfl⟩ := hj1
    obtain ⟨m, ⟨h3, _⟩, h⟩ := hj2
    omega

/-- the transformed main term. -/
def Tsum (F : Fam) (Q r M : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 M, ((Nat.totient k : ℝ) / k) * (1 / (r : ℝ)) *
    ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * Ecoef F.kind r k e * Lam F Q r k e t

theorem Tsum_measurable (F : Fam) (Q r M : ℕ) : Measurable (fun β : ℝ => Tsum F Q r M |β|) := by
  unfold Tsum
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun e _ => ?_)
  exact Measurable.const_mul ((Lam_measurable F Q r k e).comp measurable_abs) _

theorem abs_Tsum_le (F : Fam) (Q r M : ℕ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (t : ℝ) :
    |Tsum F Q r M t| ≤ ∑ k ∈ Finset.Icc 1 M, |((Nat.totient k : ℝ) / k) * (1 / (r : ℝ))| *
      ∑ e ∈ Finset.Icc 1 Q, |cE F.kind e * Ecoef F.kind r k e| * (r * Q ^ 2) := by
  unfold Tsum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_Lam_le F Q r k e hQ hr hk1 t) (abs_nonneg _)

/-- `mainSum = ∫ T(|β|)`. -/
theorem mainSum_eq (F : Fam) (Q r : ℕ) (η δ : ℝ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (hδ : 0 < δ) :
    mainSum F Q r η δ
      = ∫ β in (η - δ / 2)..(η + δ / 2), Tsum F Q r (⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ + 1) |β| := by
  set M : ℕ := ⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ + 1 with hM
  have hLint : ∀ k e : ℕ, 1 ≤ k → ∀ (g : ℝ → ℝ), (g = fun β => Lam F Q r k e β) ∨ (g = fun β => Lam F Q r k e (-β))
      ∨ (g = fun β => Lam F Q r k e |β|) → IntervalIntegrable g volume (η - δ / 2) (η + δ / 2) := by
    intro k e hk g hg
    have hmeas : Measurable g := by
      rcases hg with rfl | rfl | rfl
      · exact Lam_measurable F Q r k e
      · exact (Lam_measurable F Q r k e).comp measurable_neg
      · exact (Lam_measurable F Q r k e).comp measurable_abs
    apply intervalIntegrable_of_bdd hmeas (r * Q ^ 2)
    intro x
    rcases hg with rfl | rfl | rfl <;> exact abs_Lam_le F Q r k e hQ hr hk _
  have hsum : mainSum F Q r η δ = ∑ k ∈ Finset.Icc 1 M, ((Nat.totient k : ℝ) / k) * (1 / (r : ℝ)) *
      ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * Ecoef F.kind r k e *
        ∫ β in (η - δ / 2)..(η + δ / 2), Lam F Q r k e |β| := by
    simp only [mainSum]
    rw [sum_lines M]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [← mul_add, lineInt_pos F Q r k e η δ hQ hr hk1 hδ, lineInt_neg F Q r k e η δ hQ hr hk1 hδ,
      ← intervalIntegral.integral_add (hLint k e hk1 _ (Or.inl rfl)) (hLint k e hk1 _ (Or.inr (Or.inl rfl)))]
    congr 1
    apply intervalIntegral.integral_congr
    intro β _
    exact Lam_add_neg F Q r k e hQ hr hk1 β
  rw [hsum]
  unfold Tsum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum]
    · congr 1
      apply Finset.sum_congr rfl
      intro e _
      rw [intervalIntegral.integral_const_mul]
    · intro e _
      exact (hLint k e hk1 _ (Or.inr (Or.inr rfl))).const_mul _
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    apply IntervalIntegrable.const_mul
    apply intervalIntegrable_of_bdd (Finset.measurable_sum _ (fun e _ =>
      Measurable.const_mul ((Lam_measurable F Q r k e).comp measurable_abs) _))
      (∑ e ∈ Finset.Icc 1 Q, |cE F.kind e * Ecoef F.kind r k e| * (r * Q ^ 2))
    intro β
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun e _ => ?_))
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_Lam_le F Q r k e hQ hr hk1 _) (abs_nonneg _)

/-- the pointwise comparison: only the lines `kQ < v` (points `q < 1`) differ. -/
theorem pointwise_diff (F : Fam) (Q r M : ℕ) (t : ℝ) (hQ : 1 ≤ Q) (hr : 1 ≤ r) (ht : 0 ≤ t)
    (hM : (r : ℝ) * Q * t ≤ M) :
    |Tsum F Q r M t - (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * t)|
      ≤ BE * ∑ e ∈ Finset.Icc 1 ⌊(r : ℝ) * Q * t⌋₊, |cE F.kind e| := by
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hBE : 0 ≤ BE := by unfold BE; positivity
  have hS0 : 0 ≤ ∑ e ∈ Finset.Icc 1 ⌊(r : ℝ) * Q * t⌋₊, |cE F.kind e| :=
    Finset.sum_nonneg (fun e _ => abs_nonneg _)
  rcases ht.lt_or_eq with htp | ht0
  swap
  · -- t = 0
    subst ht0
    have hL : ∀ k e : ℕ, 1 ≤ k → Lam F Q r k e 0 = 0 := by
      intro k e hk
      unfold Lam
      rw [Set.indicator_of_notMem]
      intro h
      have : 0 < (k : ℝ) / (r * Q) := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        positivity
      linarith [h.1]
    have hT : Tsum F Q r M 0 = 0 := by
      unfold Tsum
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.sum_eq_zero (fun e _ => by rw [hL k e (Finset.mem_Icc.mp hk).1, mul_zero]), mul_zero]
    rw [hT, mul_zero, gProf_eq_zero_of_lt_one F r (by norm_num), mul_zero, sub_zero, abs_zero]
    exact mul_nonneg hBE (Finset.sum_nonneg (fun e _ => abs_nonneg _))
  set v : ℝ := (r : ℝ) * Q * t with hv
  have hv0 : 0 < v := by positivity
  set N : ℕ := ⌊v⌋₊ with hN
  have hNv : (N : ℝ) ≤ v := Nat.floor_le hv0.le
  have hNM : N ≤ M := by
    have : (N : ℝ) ≤ M := hNv.trans hM
    exact_mod_cast this
  set X : ℕ → ℝ := fun k => ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * Ecoef F.kind r k e * F.w ((k : ℝ) * e / v)
    with hX
  set Y : ℕ → ℝ := fun k => ∑ e ∈ Finset.Icc 1 N, cE F.kind e * Ecoef F.kind r k e * F.w ((k : ℝ) * e / v)
    with hY
  -- the main term, line by line
  have hterm : ∀ k ∈ Finset.Icc 1 M, ((Nat.totient k : ℝ) / k) * (1 / (r : ℝ)) *
      ∑ e ∈ Finset.Icc 1 Q, cE F.kind e * Ecoef F.kind r k e * Lam F Q r k e t
      = (Q : ℝ) ^ 2 / v ^ 2 * ((Nat.totient k : ℝ) * (if (k : ℝ) ≤ v ∧ v ≤ k * Q then X k else 0)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk1
    have hmem : t ∈ Set.Icc ((k : ℝ) / (r * Q)) ((k : ℝ) / r) ↔ (k : ℝ) ≤ v ∧ v ≤ k * Q := by
      have hrQ0 : (0 : ℝ) < r * Q := by positivity
      have hr0 : (0 : ℝ) < r := by positivity
      have hQ0 : (0 : ℝ) < Q := by positivity
      rw [Set.mem_Icc, div_le_iff₀ hrQ0, le_div_iff₀ hr0, hv]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨by linarith, ?_⟩
        have := mul_le_mul_of_nonneg_right h2 hQ0.le
        linarith
      · rintro ⟨h1, h2⟩
        refine ⟨by linarith, ?_⟩
        by_contra hcon
        push_neg at hcon
        have := mul_lt_mul_of_pos_right hcon hQ0
        linarith
    by_cases hc : (k : ℝ) ≤ v ∧ v ≤ k * Q
    · rw [if_pos hc]
      have hL : ∀ e : ℕ, Lam F Q r k e t = (k : ℝ) / (r * t ^ 2) * F.w ((k : ℝ) * e / v) := by
        intro e
        unfold Lam
        rw [Set.indicator_of_mem (hmem.mpr hc)]
        have harg : (k : ℝ) / (r * t) * e / Q = (k : ℝ) * e / v := by rw [hv]; field_simp
        simp only [harg]
      simp only [hL, hX]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [hv]
      field_simp
    · rw [if_neg hc]
      have hL : ∀ e : ℕ, Lam F Q r k e t = 0 := by
        intro e
        unfold Lam
        rw [Set.indicator_of_notMem (fun h => hc (hmem.mp h))]
      simp only [hL, mul_zero, Finset.sum_const_zero]
  have hprof : (Q : ℝ) ^ 2 * gProf F r v = (Q : ℝ) ^ 2 / v ^ 2 * ∑ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * Y k := by
    unfold gProf
    rw [← hN]
    simp only [hY]
    rw [div_eq_mul_inv]
    rw [mul_assoc]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  -- restrict the main term to `k ≤ N`
  have hrestr : ∑ k ∈ Finset.Icc 1 M, (Nat.totient k : ℝ) * (if (k : ℝ) ≤ v ∧ v ≤ k * Q then X k else 0)
      = ∑ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then X k else 0) := by
    symm
    apply Finset.sum_subset_zero_on_sdiff
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk
      rw [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Icc] at hk
      have hkN : N < k := by omega
      have hkv : v < k := by
        have hfl := Nat.lt_floor_add_one v
        have hNk : ((N : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast hkN
        linarith
      rw [if_neg (fun h => by linarith [h.1]), mul_zero]
    · intro k hk
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      have hkv : (k : ℝ) ≤ v := le_trans (by exact_mod_cast hkN) hNv
      by_cases h : v ≤ k * Q
      · rw [if_pos h, if_pos ⟨hkv, h⟩]
      · rw [if_neg h, if_neg (fun h' => h h'.2)]
  -- for `v ≤ kQ` the two `e`-ranges give the same sum
  have hXY : ∀ k ∈ Finset.Icc 1 N, v ≤ k * Q → X k = Y k := by
    intro k hk hkQ
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hzero : ∀ e : ℕ, v < (k : ℝ) * e → F.w ((k : ℝ) * e / v) = 0 := by
      intro e he
      apply w_eq_zero_gt1
      rw [lt_div_iff₀ hv0]; linarith
    simp only [hX, hY]
    rw [← Finset.sum_subset (Finset.inter_subset_left (s₁ := Finset.Icc 1 Q) (s₂ := Finset.Icc 1 N)),
      ← Finset.sum_subset (Finset.inter_subset_right (s₁ := Finset.Icc 1 Q) (s₂ := Finset.Icc 1 N))]
    · intro e he hn
      rw [Finset.mem_inter, not_and] at hn
      have heQ : e ∉ Finset.Icc 1 Q := fun h => hn h he
      rw [Finset.mem_Icc] at he heQ
      have : Q < e := by omega
      have hQe : (Q : ℝ) < e := by exact_mod_cast this
      rw [hzero e (by nlinarith), mul_zero]
    · intro e he hn
      rw [Finset.mem_inter] at hn
      have heN : e ∉ Finset.Icc 1 N := fun h => hn ⟨he, h⟩
      rw [Finset.mem_Icc] at he heN
      have hNe : N < e := by omega
      have hve : v < e := by
        have hfl := Nat.lt_floor_add_one v
        have hNe' : ((N : ℕ) : ℝ) + 1 ≤ e := by exact_mod_cast hNe
        linarith
      rw [hzero e (by nlinarith), mul_zero]
  -- assemble
  have hT : Tsum F Q r M t = (Q : ℝ) ^ 2 / v ^ 2 *
      ∑ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then X k else 0) := by
    unfold Tsum
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hrestr]
  rw [hT, hprof, ← mul_sub, ← Finset.sum_sub_distrib]
  have hdiff : ∀ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then X k else 0)
      - (Nat.totient k : ℝ) * Y k = -((Nat.totient k : ℝ) * (if v ≤ k * Q then 0 else Y k)) := by
    intro k hk
    by_cases h : v ≤ k * Q
    · rw [if_pos h, if_pos h, hXY k hk h]; ring
    · rw [if_neg h, if_neg h]; ring
  rw [Finset.sum_congr rfl hdiff, Finset.sum_neg_distrib, mul_neg, abs_neg]
  set S := ∑ e ∈ Finset.Icc 1 N, |cE F.kind e| with hS
  have hYb : ∀ k, |Y k| ≤ BE * S := by
    intro k
    simp only [hY]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    rw [abs_mul, abs_mul]
    have h1 := abs_Ecoef_le F.kind r k e
    have h2 := abs_w_le_one F ((k : ℝ) * e / v)
    calc |cE F.kind e| * |Ecoef F.kind r k e| * |F.w ((k : ℝ) * e / v)| ≤ |cE F.kind e| * BE * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2 (abs_nonneg _)
          exact mul_nonneg (abs_nonneg _) hBE
      _ = BE * |cE F.kind e| := by ring
  set x : ℝ := v / Q with hx
  have hx0 : 0 ≤ x := by positivity
  have hsumk : ∑ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then 0 else BE * S) ≤ x ^ 2 * (BE * S) := by
    have hBS : 0 ≤ BE * S := mul_nonneg hBE (by rw [hS]; exact Finset.sum_nonneg (fun e _ => abs_nonneg _))
    have h1 : ∀ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then 0 else BE * S)
        ≤ (if (k : ℝ) ≤ x then x else 0) * (BE * S) := by
      intro k _
      by_cases h : v ≤ k * Q
      · rw [if_pos h, mul_zero]
        split_ifs <;> positivity
      · rw [if_neg h]
        have hkx : (k : ℝ) < x := by
          rw [hx, lt_div_iff₀ (by positivity)]; linarith
        rw [if_pos hkx.le]
        apply mul_le_mul_of_nonneg_right _ hBS
        have := Nat.totient_le k
        have : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast this
        linarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hBS
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 N).filter (fun k : ℕ => (k : ℝ) ≤ x)).card ≤ ⌊x⌋₊ := by
      calc ((Finset.Icc 1 N).filter (fun k : ℕ => (k : ℝ) ≤ x)).card ≤ (Finset.Icc 1 ⌊x⌋₊).card := by
            apply Finset.card_le_card
            intro k hk
            rw [Finset.mem_filter, Finset.mem_Icc] at hk
            rw [Finset.mem_Icc]
            exact ⟨hk.1.1, Nat.le_floor hk.2⟩
        _ = ⌊x⌋₊ := by simp
    have : (((Finset.Icc 1 N).filter (fun k : ℕ => (k : ℝ) ≤ x)).card : ℝ) ≤ x :=
      le_trans (by exact_mod_cast hcard) (Nat.floor_le hx0)
    nlinarith
  have hQv : (Q : ℝ) ^ 2 / v ^ 2 * x ^ 2 = 1 := by rw [hx]; field_simp
  calc |(Q : ℝ) ^ 2 / v ^ 2 * ∑ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then 0 else Y k)|
      ≤ (Q : ℝ) ^ 2 / v ^ 2 * ∑ k ∈ Finset.Icc 1 N, (Nat.totient k : ℝ) * (if v ≤ k * Q then 0 else BE * S) := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
        rw [abs_mul, abs_of_nonneg (by positivity)]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        split_ifs
        · simp
        · exact hYb k
    _ ≤ (Q : ℝ) ^ 2 / v ^ 2 * (x ^ 2 * (BE * S)) := mul_le_mul_of_nonneg_left hsumk (by positivity)
    _ = BE * S := by rw [← mul_assoc, hQv, one_mul]

/-- `Σ_{e≤⌊y⌋} |c_e| ≤ C (1 + log y)` for both kinds. -/
theorem sum_abs_cE_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : FKind) (y : ℝ), 1 ≤ y →
    ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE k e| ≤ C * (1 + Real.log y) := by
  obtain ⟨Cq, hCq, hq⟩ := ZetaShell.MuSqPhi.musq_phi_sum_le
  refine ⟨Cq + 1, by positivity, fun k y hy => ?_⟩
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  cases k
  · have h1 : ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE FKind.plain e| ≤ ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) / e := by
      apply Finset.sum_le_sum
      intro e he
      have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
      have heR : (0 : ℝ) < e := by exact_mod_cast he1
      simp only [cE]
      rw [abs_div, abs_of_pos heR]
      apply div_le_div_of_nonneg_right _ heR.le
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 := ZetaShell.MuSqPhi.sum_inv_le ⌊y⌋₊
    have hNy : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le (by linarith)
    have hN1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
    have h3 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y := Real.log_le_log (by exact_mod_cast hN1) hNy
    have : (1 + Real.log y) ≤ (Cq + 1) * (1 + Real.log y) := by nlinarith
    linarith
  · have h1 : ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |cE FKind.qphi e|
        = ∑ e ∈ Finset.Icc 1 ⌊y⌋₊, |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [cE]
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient e : ℝ))]
    rw [h1]
    refine (hq y hy).trans ?_
    nlinarith

theorem step4_profile (F : Fam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q r : ℕ) (η δ : ℝ), 2 ≤ Q → 1 ≤ r → r ≤ Q → |η| ≤ 1 / (r : ℝ) → 0 < δ → δ < 1 →
      |mainSum F Q r η δ - mProf F Q r η δ| ≤ C * δ * (1 + Real.log Q) := by
  obtain ⟨Cc, hCc, hc⟩ := sum_abs_cE_le
  have hBE : 0 ≤ BE := by unfold BE; positivity
  refine ⟨2 * BE * Cc, by positivity, ?_⟩
  intro Q r η δ hQ hr hrQ hη hδ hδ1
  have hQ1 : 1 ≤ Q := by omega
  have hQR : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrQR : (r : ℝ) ≤ Q := by exact_mod_cast hrQ
  set M : ℕ := ⌊(r : ℝ) * Q * (|η| + δ / 2)⌋₊ + 1 with hM
  set a := η - δ / 2 with ha
  set b := η + δ / 2 with hb
  have hab : a ≤ b := by linarith
  -- the pointwise bound on the window
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hpt : ∀ β ∈ Set.uIoc a b,
      |Tsum F Q r M (abs β) - (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β))| ≤ 2 * BE * Cc * (1 + Real.log Q) := by
    intro β hβ
    rw [Set.uIoc_of_le hab] at hβ
    have hβη : |β| ≤ |η| + δ / 2 := by
      have h1 : |β| ≤ |η| + |β - η| := by
        have := abs_add_le η (β - η); simp only [add_sub_cancel] at this; exact this
      have h2 : |β - η| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith [hβ.1, hβ.2]
      linarith
    have hvM : (r : ℝ) * Q * |β| ≤ M := by
      have h1 : (r : ℝ) * Q * |β| ≤ (r : ℝ) * Q * (|η| + δ / 2) :=
        mul_le_mul_of_nonneg_left hβη (by positivity)
      have h2 := Nat.lt_floor_add_one ((r : ℝ) * Q * (|η| + δ / 2))
      rw [hM]; push_cast; linarith
    refine (pointwise_diff F Q r M |β| hQ1 hr (abs_nonneg β) hvM).trans ?_
    set v := (r : ℝ) * Q * |β| with hv
    by_cases hv1 : 1 ≤ v
    · have hS := hc F.kind v hv1
      -- `v ≤ Q²`
      have hvQ : v ≤ (Q : ℝ) ^ 2 := by
        have h1 : |β| ≤ 1 / (r : ℝ) + 1 / 2 := by linarith
        have h2 : v ≤ (r : ℝ) * Q * (1 / r + 1 / 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (r : ℝ) * Q * (1 / r + 1 / 2) = Q + r * Q / 2 := by field_simp
        nlinarith
      have hlogv : Real.log v ≤ 2 * Real.log Q := by
        have := Real.log_le_log (by linarith) hvQ
        rw [Real.log_pow] at this; push_cast at this; linarith
      have : 1 + Real.log v ≤ 2 * (1 + Real.log Q) := by linarith
      calc BE * ∑ e ∈ Finset.Icc 1 ⌊v⌋₊, |cE F.kind e| ≤ BE * (Cc * (1 + Real.log v)) :=
            mul_le_mul_of_nonneg_left hS hBE
        _ ≤ BE * (Cc * (2 * (1 + Real.log Q))) := by
            apply mul_le_mul_of_nonneg_left _ hBE
            exact mul_le_mul_of_nonneg_left this hCc
        _ = 2 * BE * Cc * (1 + Real.log Q) := by ring
    · push_neg at hv1
      have hfl : ⌊v⌋₊ = 0 := Nat.floor_eq_zero.mpr hv1
      rw [hfl]
      simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty, mul_zero]
      positivity
  -- integrability
  have hTint : IntervalIntegrable (fun β => Tsum F Q r M (abs β)) volume a b :=
    intervalIntegrable_of_bdd (Tsum_measurable F Q r M) _ (fun β => abs_Tsum_le F Q r M hQ1 hr |β|) a b
  have hPmeas : Measurable (fun β : ℝ => (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β))) :=
    measurable_const.mul ((measurable_gProf F r).comp (measurable_const.mul measurable_abs))
  have hPint : IntervalIntegrable (fun β : ℝ => (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β))) volume a b := by
    refine IntervalIntegrable.mono_fun' (g := fun β => abs (Tsum F Q r M (abs β)) + 2 * BE * Cc * (1 + Real.log Q))
      (hTint.abs.add intervalIntegrable_const) hPmeas.aestronglyMeasurable ?_
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun β hβ => ?_)
    rw [Real.norm_eq_abs]
    have h := hpt β hβ
    have h2 : |(Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β))|
        ≤ abs (Tsum F Q r M (abs β)) + abs (Tsum F Q r M (abs β) - (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β))) := by
      have := abs_sub_abs_le_abs_sub ((Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β))) (Tsum F Q r M (abs β))
      rw [abs_sub_comm] at this
      linarith
    linarith
  rw [mainSum_eq F Q r η δ hQ1 hr hδ]
  have hm : mProf F Q r η δ = ∫ β in a..b, (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β)) := rfl
  rw [hm, ← intervalIntegral.integral_sub hTint hPint]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun β => Tsum F Q r M (abs β) - (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β)))
    (fun β hβ => by rw [Real.norm_eq_abs]; exact hpt β hβ)
  rw [Real.norm_eq_abs] at hnorm
  have hba : |b - a| = δ := by rw [hb, ha]; rw [show η + δ / 2 - (η - δ / 2) = δ by ring, abs_of_pos hδ]
  rw [hba] at hnorm
  calc |∫ β in a..b, (Tsum F Q r M (abs β) - (Q : ℝ) ^ 2 * gProf F r ((r : ℝ) * Q * (abs β)))|
      ≤ 2 * BE * Cc * (1 + Real.log Q) * δ := hnorm
    _ = 2 * BE * Cc * δ * (1 + Real.log Q) := by ring

end TrackF
end ZetaShell

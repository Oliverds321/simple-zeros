/-
L7_5 (28 Sep 2026), round 5: `ZR_phi_bounds'` (the statement of the shared leaf `ZR_phi_bounds`), PROVED from the
POINTWISE leaf `ZR_phi_pw` by integrating over the set
  `K = {u : |u − s| ≤ κ, |e^u − x| ≤ 1/(8Δ)}`, `vol K ≤ 2 min(1/Δ, N)/N` (`ZRK_volume`, via the diameter),
and `e^{(a−1/2)u} ≤ 2 N^{a−1/2}` on `K` (`0 ≤ a ≤ 1`, `κ ≤ 1`).
`ZR_phi_pw`: on `K`, `|φ_x(u)| ≤ C T e^{−u/2}` and `|φ_x″(u)| ≤ C X² T e^{−u/2}` (`X = T+ΔN+1`), both `0` off `K`.
Its first half is `ZR_phi_pw0` (PROVED, ZR_PhiPw0.lean); its second half `ZR_phi_pw2` is proved from `ZR_phi2_zero` (vanishing off `K`, proved) and the leaf
`ZR_phi_pw2K` (the bound ON `K`), PROVED in round 6 via `ZR_phi_pw2K'` (ZR_Phi2.lean); it needed `|D_T| ≤ T`, `|D_T′| ≤ 2T²`, `|D_T″| ≪ T³`, `Δe^u ≤ 3X` on `K`, and the chain rule for `f(Δ(e^u − x))`.
-/
import ZetaShell.PropZ.ZR_Phi2

open MeasureTheory

namespace ZetaShell.PropZ

/-- the `u`-set carrying `φ_x(u) = V_{x,s}(e^u)`. -/
def ZRK (s κ Δ x : ℝ) : Set ℝ := {u | |u - s| ≤ κ ∧ |Real.exp u - x| ≤ 1 / (8 * Δ)}

theorem ZRK_isClosed (s κ Δ x : ℝ) : IsClosed (ZRK s κ Δ x) :=
  (isClosed_le (f := fun u : ℝ => |u - s|) (g := fun _ => κ) (by fun_prop) continuous_const).inter
    (isClosed_le (f := fun u : ℝ => |Real.exp u - x|) (g := fun _ => 1 / (8 * Δ)) (by fun_prop) continuous_const)

/-- the open core of `ZR_phi_pw`: the second-derivative bound ON `K` (vanishing off `K` is proved below). -/
theorem ZR_phi_pw2K (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 → ∀ (x u : ℝ),
      u ∈ ZRK s κ Δ x →
      ‖deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u‖
          ≤ C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp (-(u / 2)) := by
  obtain ⟨C, hC, h⟩ := ZR_phi_pw2K' κ hκ hκ1 Ξ hΞ f hf
  exact ⟨C, hC, fun s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u hu => h s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u hu.1⟩

/-- `φ″ = 0` off `K`: `tsupport φ″ ⊆ tsupport φ ⊆ K` (from `ZR_phi_pw0`, `K` closed). -/
theorem ZR_phi2_zero (κ : ℝ) (hκ : 0 < κ) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (f : ℝ → ℝ) (hf : TestFn f)
    (T Δ s x : ℝ) (hT : 0 ≤ T) (hΔ : 0 < Δ) (u : ℝ) (hu : u ∉ ZRK s κ Δ x) :
    deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u = 0 := by
  obtain ⟨C₀, _, h0⟩ := ZR_phi_pw0 κ hκ Ξ hΞ f hf
  have hsupp : Function.support (fun u => VxsW T κ Ξ f Δ s x (Real.exp u)) ⊆ ZRK s κ Δ x := by
    intro v hv
    by_contra hvK
    apply hv
    have h := h0 T Δ s hT hΔ x v
    have hind : ({u | |u - s| ≤ κ ∧ |Real.exp u - x| ≤ 1 / (8 * Δ)} : Set ℝ).indicator (fun _ => (1 : ℝ)) v = 0 :=
      Set.indicator_of_notMem hvK _
    rw [hind, mul_zero] at h
    exact norm_le_zero_iff.mp h
  have hts : tsupport (fun u => VxsW T κ Ξ f Δ s x (Real.exp u)) ⊆ ZRK s κ Δ x :=
    closure_minimal hsupp (ZRK_isClosed s κ Δ x)
  have h2 : u ∉ tsupport (deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u)))) := fun h =>
    hu (hts (tsupport_deriv_subset (tsupport_deriv_subset h)))
  exact image_eq_zero_of_notMem_tsupport h2

theorem ZR_phi_pw2 (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 → ∀ (x u : ℝ),
      ‖deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u‖
          ≤ C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp (-(u / 2))
            * (ZRK s κ Δ x).indicator (fun _ => (1 : ℝ)) u := by
  obtain ⟨C, hC, hK⟩ := ZR_phi_pw2K κ hκ hκ1 Ξ hΞ f hf
  refine ⟨C, hC, fun s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u => ?_⟩
  by_cases hu : u ∈ ZRK s κ Δ x
  · rw [Set.indicator_of_mem hu, mul_one]; exact hK s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u hu
  · rw [Set.indicator_of_notMem hu, mul_zero, ZR_phi2_zero κ hκ Ξ hΞ f hf T Δ s x (by linarith) hΔ u hu,
      norm_zero]

theorem ZR_phi_pw (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 → ∀ (x u : ℝ),
      ‖VxsW T κ Ξ f Δ s x (Real.exp u)‖
          ≤ C * T * Real.exp (-(u / 2)) * (ZRK s κ Δ x).indicator (fun _ => (1 : ℝ)) u ∧
      ‖deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u‖
          ≤ C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp (-(u / 2))
            * (ZRK s κ Δ x).indicator (fun _ => (1 : ℝ)) u := by
  obtain ⟨C₀, hC₀, h0⟩ := ZR_phi_pw0 κ hκ Ξ hΞ f hf
  obtain ⟨C₂, hC₂, h2⟩ := ZR_phi_pw2 κ hκ hκ1 Ξ hΞ f hf
  refine ⟨max C₀ C₂, le_max_of_le_left hC₀, fun s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u => ⟨?_, ?_⟩⟩
  · have hind : 0 ≤ (ZRK s κ Δ x).indicator (fun _ => (1 : ℝ)) u :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) u
    exact (h0 T Δ s (by linarith) hΔ x u).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) (Real.exp_pos _).le) hind)
  · have hind : 0 ≤ (ZRK s κ Δ x).indicator (fun _ => (1 : ℝ)) u :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) u
    exact (h2 s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) (by linarith)) (Real.exp_pos _).le) hind)

theorem ZRK_measurable (s κ Δ x : ℝ) : MeasurableSet (ZRK s κ Δ x) := by
  unfold ZRK
  exact ((isClosed_le (f := fun u : ℝ => |u - s|) (g := fun _ => κ) (by fun_prop) continuous_const).inter
    (isClosed_le (f := fun u : ℝ => |Real.exp u - x|) (g := fun _ => 1 / (8 * Δ)) (by fun_prop)
      continuous_const)).measurableSet

theorem ZRK_sub (s κ Δ x : ℝ) : ZRK s κ Δ x ⊆ Set.Icc (s - κ) (s + κ) := fun u hu => by
  have := abs_le.mp hu.1; constructor <;> linarith

theorem ZRK_volume (s₀ s κ Δ x : ℝ) (hκ1 : κ ≤ 1) (hs₀ : 3 ≤ s₀) (hs : |s - s₀| ≤ 1) (hΔ : 0 < Δ) :
    volume.real (ZRK s κ Δ x) ≤ 2 * min (1 / Δ) (Real.exp s) / Real.exp s := by
  have hN0 := Real.exp_pos s
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  set D := 2 * min (1 / Δ) (Real.exp s) / Real.exp s with hD
  have hD0 : 0 ≤ D := by rw [hD]; have : 0 ≤ min (1 / Δ) (Real.exp s) := le_min (by positivity) hN0.le
                         positivity
  have hd : ∀ u₁ ∈ ZRK s κ Δ x, ∀ u₂ ∈ ZRK s κ Δ x, u₁ ≤ u₂ → u₂ - u₁ ≤ D := by
    intro u₁ h₁ u₂ h₂ h12
    obtain ⟨h1a, h1b⟩ := h₁
    obtain ⟨h2a, h2b⟩ := h₂
    have ha1 := abs_le.mp h1a
    have ha2 := abs_le.mp h2a
    have hb1 := abs_le.mp h1b
    have hb2 := abs_le.mp h2b
    have hA : u₂ - u₁ ≤ 2 := by linarith
    have he1 : Real.exp u₁ * (1 + (u₂ - u₁)) ≤ Real.exp u₂ := by
      have h := Real.add_one_le_exp (u₂ - u₁)
      calc Real.exp u₁ * (1 + (u₂ - u₁)) ≤ Real.exp u₁ * Real.exp (u₂ - u₁) :=
            mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
        _ = Real.exp u₂ := by rw [← Real.exp_add]; ring_nf
    have hlow : Real.exp s ≤ 3 * Real.exp u₁ := by
      calc Real.exp s ≤ Real.exp (u₁ + 1) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp u₁ * Real.exp 1 := Real.exp_add u₁ 1
        _ ≤ Real.exp u₁ * 3 := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
        _ = 3 * Real.exp u₁ := by ring
    have h8 : 1 / (8 * Δ) = (1 / Δ) / 8 := by field_simp
    have hB : Real.exp u₁ * (u₂ - u₁) ≤ (1 / Δ) / 4 := by nlinarith
    have hB' : Real.exp s * (u₂ - u₁) ≤ 3 * (1 / Δ) / 4 := by nlinarith
    rw [hD]
    rcases min_cases (1 / Δ) (Real.exp s) with ⟨hm, _⟩ | ⟨hm, hlt⟩
    · rw [hm, le_div_iff₀ hN0]; nlinarith [one_div_pos.mpr hΔ]
    · rw [hm, mul_div_assoc, div_self hN0.ne']; linarith
  have hdiam : EMetric.diam (ZRK s κ Δ x) ≤ ENNReal.ofReal D := by
    refine EMetric.diam_le fun u₁ h₁ u₂ h₂ => ?_
    rw [edist_dist, Real.dist_eq]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total u₁ u₂ with h | h
    · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; exact hd u₁ h₁ u₂ h₂ h
    · rw [abs_of_nonneg (by linarith)]; exact hd u₂ h₂ u₁ h₁ h
  exact ENNReal.toReal_le_of_le_ofReal hD0 ((Real.volume_le_diam _).trans hdiam)

theorem ZR_int_indicator (s₀ s κ Δ x a B : ℝ) (hκ1 : κ ≤ 1) (hs₀ : 3 ≤ s₀) (hs : |s - s₀| ≤ 1)
    (hΔ : 0 < Δ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hB : 0 ≤ B) (g : ℝ → ℝ) (hg0 : ∀ u, 0 ≤ g u)
    (hg : ∀ u, g u ≤ B * Real.exp (-(u / 2)) * (ZRK s κ Δ x).indicator (fun _ => (1 : ℝ)) u) :
    (∫ u, g u * Real.exp (a * u))
      ≤ B * 2 * Real.exp s ^ (a - 1 / 2) * (2 * min (1 / Δ) (Real.exp s) / Real.exp s) := by
  set K := ZRK s κ Δ x with hK
  have hmK := ZRK_measurable s κ Δ x
  have hB2 : 0 ≤ B * 2 * Real.exp s ^ (a - 1 / 2) := mul_nonneg (mul_nonneg hB (by norm_num)) (by positivity)
  have hexp2 : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have e : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hpw : ∀ u, g u * Real.exp (a * u) ≤ K.indicator (fun _ => B * 2 * Real.exp s ^ (a - 1 / 2)) u := by
    intro u
    by_cases hu : u ∈ K
    · rw [Set.indicator_of_mem hu]
      have h := hg u
      rw [Set.indicator_of_mem hu, mul_one] at h
      have hq := abs_le.mp hu.1
      have hprod : (a - 1 / 2) * (u - s) ≤ 1 / 2 := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - (a - 1 / 2) by linarith) (show (0 : ℝ) ≤ 1 + (u - s) by linarith),
          mul_nonneg (show (0 : ℝ) ≤ 1 / 2 + (a - 1 / 2) by linarith) (show (0 : ℝ) ≤ 1 - (u - s) by linarith)]
      have hE : Real.exp (-(u / 2)) * Real.exp (a * u) ≤ 2 * Real.exp s ^ (a - 1 / 2) := by
        rw [← Real.exp_add, ← Real.exp_mul]
        calc Real.exp (-(u / 2) + a * u) ≤ Real.exp (1 / 2 + s * (a - 1 / 2)) :=
              Real.exp_le_exp.mpr (by nlinarith)
          _ = Real.exp (1 / 2) * Real.exp (s * (a - 1 / 2)) := Real.exp_add _ _
          _ ≤ 2 * Real.exp (s * (a - 1 / 2)) :=
              mul_le_mul_of_nonneg_right hexp2 (Real.exp_pos _).le
      calc g u * Real.exp (a * u) ≤ B * Real.exp (-(u / 2)) * Real.exp (a * u) :=
            mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
        _ = B * (Real.exp (-(u / 2)) * Real.exp (a * u)) := by ring
        _ ≤ B * (2 * Real.exp s ^ (a - 1 / 2)) := mul_le_mul_of_nonneg_left hE hB
        _ = B * 2 * Real.exp s ^ (a - 1 / 2) := by ring
    · rw [Set.indicator_of_notMem hu]
      have h := hg u
      rw [Set.indicator_of_notMem hu, mul_zero] at h
      have : g u = 0 := le_antisymm h (hg0 u)
      rw [this, zero_mul]
  have hfin : volume K ≠ ⊤ :=
    ((measure_mono (ZRK_sub s κ Δ x)).trans_lt measure_Icc_lt_top).ne
  have hint : Integrable (K.indicator (fun _ => B * 2 * Real.exp s ^ (a - 1 / 2))) :=
    (integrableOn_const (hs := hfin)).integrable_indicator hmK
  calc (∫ u, g u * Real.exp (a * u))
      ≤ ∫ u, K.indicator (fun _ => B * 2 * Real.exp s ^ (a - 1 / 2)) u :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => by
          simp only [Pi.zero_apply]; exact mul_nonneg (hg0 u) (Real.exp_pos _).le)
          hint (Filter.Eventually.of_forall hpw)
    _ = volume.real K * (B * 2 * Real.exp s ^ (a - 1 / 2)) := by
        rw [integral_indicator_const _ hmK, smul_eq_mul]
    _ ≤ (2 * min (1 / Δ) (Real.exp s) / Real.exp s) * (B * 2 * Real.exp s ^ (a - 1 / 2)) :=
        mul_le_mul_of_nonneg_right (ZRK_volume s₀ s κ Δ x hκ1 hs₀ hs hΔ) hB2
    _ = _ := by ring

theorem ZR_phi_bounds' (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s₀ T Δ s : ℝ), 3 ≤ s₀ → 2 ≤ T → 0 < Δ → Δ ≤ 1 → |s - s₀| ≤ 1 →
      ∀ (x a : ℝ), 0 ≤ a → a ≤ 1 →
      (∫ u, ‖VxsW T κ Ξ f Δ s x (Real.exp u)‖ * Real.exp (a * u))
          ≤ C * T * Real.exp s ^ (a - 1 / 2) * min (1 / Δ) (Real.exp s) / Real.exp s ∧
      (∫ u, ‖deriv (deriv (fun u => VxsW T κ Ξ f Δ s x (Real.exp u))) u‖ * Real.exp (a * u))
          ≤ C * (T + Δ * Real.exp s + 1) ^ 2 * T * Real.exp s ^ (a - 1 / 2) * min (1 / Δ) (Real.exp s)
            / Real.exp s := by
  obtain ⟨C₀, hC₀, hpw⟩ := ZR_phi_pw κ hκ hκ1 Ξ hΞ f hf
  refine ⟨4 * C₀, by positivity, fun s₀ T Δ s hs₀ hT hΔ hΔ1 hs x a ha0 ha1 => ⟨?_, ?_⟩⟩
  · refine (ZR_int_indicator s₀ s κ Δ x a (C₀ * T) hκ1 hs₀ hs hΔ ha0 ha1 (by positivity) _
      (fun u => norm_nonneg _) (fun u => (hpw s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u).1)).trans (le_of_eq ?_)
    ring
  · have hX : 0 ≤ (T + Δ * Real.exp s + 1) ^ 2 := sq_nonneg _
    refine (ZR_int_indicator s₀ s κ Δ x a (C₀ * (T + Δ * Real.exp s + 1) ^ 2 * T) hκ1 hs₀ hs hΔ ha0 ha1
      (by positivity) _ (fun u => norm_nonneg _) (fun u => (hpw s₀ T Δ s hs₀ hT hΔ hΔ1 hs x u).2)).trans
      (le_of_eq ?_)
    ring

end ZetaShell.PropZ

/-
L7_9 round 4: `Σ_{m≤N}|w̃(m+1) − w̃(m)|² ≤ (8/e^{3(s−1)})·(18T²(e^{s+1} + 2) + 512T⁴(2e^{s+1}/T + 1)·Cz)`
(for `T ≥ 2`, `s ≥ 3`, `T ≤ e^{s−1}/2`): blocks `⌊T(log m − s)⌋ = k` of length `≤ 2e^{s+1}/T + 1`, on which
`|w̃(m+1) − w̃(m)| ≤ (3T + 16T²/(|k|+1))/(m√m)`.
-/
import ZetaShell.LemmaK.LK9_K6a_DiffD
import ZetaShell.LemmaK.LK9_K6a_Step2
import ZetaShell.LemmaK.LK9_K6d_Aux

noncomputable section
open Finset

namespace ZetaShell
namespace LemmaK
namespace K6

lemma rho6_zero_of {u : ℝ} (hu : 1 ≤ |u|) : rho6 u = 0 := by
  unfold rho6
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]

lemma wmod_zero_of (T s : ℝ) (n : ℕ) (hn : 1 ≤ |Real.log n - s|) : wmod T s n = 0 := by
  unfold wmod
  rw [rho6_zero_of hn]
  simp

lemma wmod_supp (T s : ℝ) (hs : 1 ≤ s) (n : ℕ) (hn : wmod T s n ≠ 0) :
    Real.exp (s - 1) < n ∧ (n : ℝ) < Real.exp (s + 1) := by
  have hlt : |Real.log n - s| < 1 := by
    by_contra hc; rw [not_lt] at hc; exact hn (wmod_zero_of T s n hc)
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0] at hlt; simp at hlt; rw [abs_of_nonneg (by linarith)] at hlt; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [abs_lt] at hlt
  constructor
  · rw [← Real.exp_log hnR]; exact Real.exp_lt_exp.mpr (by linarith)
  · rw [← Real.exp_log hnR]; exact Real.exp_lt_exp.mpr (by linarith)

theorem dw_sum (T s : ℝ) (hT : 2 ≤ T) (hs : 3 ≤ s) (hTs : T ≤ Real.exp (s - 1) / 2) (N : ℕ) :
    ∑ m ∈ Finset.Ioc 0 N, ‖wmod T s (m + 1) - wmod T s m‖ ^ 2
      ≤ 8 / Real.exp (s - 1) ^ 3 * (18 * T ^ 2 * (Real.exp (s + 1) + 2)
          + 512 * T ^ 4 * ((2 * Real.exp (s + 1) / T + 1) * Cz)) := by
  classical
  set E1 := Real.exp (s - 1) with hE1
  have hE1pos : 0 < E1 := Real.exp_pos _
  have hE12 : 2 ≤ E1 := by
    have : (2 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    exact this.trans (Real.exp_le_exp.mpr (by linarith))
  have hT0 : 0 < T := by linarith
  set F : ℕ → ℝ := fun m => ‖wmod T s (m + 1) - wmod T s m‖ ^ 2 with hF
  set rel := (Finset.Ioc 0 N).filter
    (fun m : ℕ => E1 - 1 ≤ (m : ℝ) ∧ (m : ℝ) < Real.exp (s + 1)) with hrel
  -- only `rel` contributes
  have hrelsum : ∑ m ∈ Finset.Ioc 0 N, F m = ∑ m ∈ rel, F m := by
    rw [hrel, Finset.sum_filter_of_ne]
    intro m _ hFm
    have hne : wmod T s (m + 1) - wmod T s m ≠ 0 := by
      intro h; apply hFm; simp only [hF]; rw [h, norm_zero]; norm_num
    by_cases h1 : wmod T s (m + 1) = 0
    · have h2 : wmod T s m ≠ 0 := by intro h2; apply hne; rw [h1, h2, sub_zero]
      have := wmod_supp T s (by linarith) m h2
      exact ⟨by linarith [this.1], this.2⟩
    · have := wmod_supp T s (by linarith) (m + 1) h1
      push_cast at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- the per-term bound
  set g : ℕ → ℤ := fun m => ⌊T * (Real.log m - s)⌋ with hg
  have hterm : ∀ m ∈ rel, F m ≤ 8 / E1 ^ 3 * (18 * T ^ 2 + 512 * T ^ 4 * (1 / (((g m : ℤ) : ℝ) ^ 2 + 1))) := by
    intro m hm
    rw [hrel, Finset.mem_filter] at hm
    have hmlow : E1 / 2 ≤ (m : ℝ) := by linarith [hm.2.1]
    have hmT : T ≤ (m : ℝ) := hTs.trans hmlow
    have hm1 : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by linarith)
    have hm0 : (0 : ℝ) < m := by linarith
    have hstep := wmod_step2 T s hT0.le m hm1
    have hD := dD_block T s (by linarith) m hmT
    set q := Real.sqrt m with hq
    have hq0 : 0 < q := Real.sqrt_pos.mpr hm0
    have hq2 : q ^ 2 = m := Real.sq_sqrt hm0.le
    set K := |(((g m) : ℤ) : ℝ)| with hK
    have hK0 : 0 ≤ K := abs_nonneg _
    have hpi : (2 * Real.pi)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; linarith [Real.pi_gt_three]
    have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    -- `‖Δw̃‖ ≤ (3T + 16T²/(K+1))/(m q)`
    have hB : ‖wmod T s (m + 1) - wmod T s m‖ ≤ (3 * T + 16 * T ^ 2 / (K + 1)) / ((m : ℝ) * q) := by
      refine hstep.trans ?_
      have h1 : (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * q)) * T ≤ 3 * T / ((m : ℝ) * q) := by
        have : 3 / ((m : ℝ) * q) * T = 3 * T / ((m : ℝ) * q) := by ring
        calc (2 * Real.pi)⁻¹ * (3 / ((m : ℝ) * q)) * T
            = (2 * Real.pi)⁻¹ * (3 * T / ((m : ℝ) * q)) := by ring
          _ ≤ 1 * (3 * T / ((m : ℝ) * q)) := mul_le_mul_of_nonneg_right hpi (by positivity)
          _ = _ := one_mul _
      have h2 : (2 * Real.pi)⁻¹ * q⁻¹ * ‖DT T (s - Real.log ((m + 1 : ℕ) : ℝ)) - DT T (s - Real.log m)‖
          ≤ 16 * T ^ 2 / (K + 1) / ((m : ℝ) * q) := by
        have hD' : ‖DT T (s - Real.log ((m + 1 : ℕ) : ℝ)) - DT T (s - Real.log m)‖
            ≤ (1 / (m : ℝ)) * (16 * T ^ 2 / (K + 1)) := hD
        calc (2 * Real.pi)⁻¹ * q⁻¹ * ‖DT T (s - Real.log ((m + 1 : ℕ) : ℝ)) - DT T (s - Real.log m)‖
            ≤ 1 * q⁻¹ * ((1 / (m : ℝ)) * (16 * T ^ 2 / (K + 1))) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hpi (by positivity)) hD'
                (norm_nonneg _) (by positivity)
          _ = 16 * T ^ 2 / (K + 1) / ((m : ℝ) * q) := by field_simp
      have e : (3 * T + 16 * T ^ 2 / (K + 1)) / ((m : ℝ) * q)
          = 3 * T / ((m : ℝ) * q) + 16 * T ^ 2 / (K + 1) / ((m : ℝ) * q) := by ring
      rw [e]; linarith
    -- square it
    have hmq : ((m : ℝ) * q) ^ 2 = (m : ℝ) ^ 3 := by rw [mul_pow, hq2]; ring
    have hm3 : (E1 / 2) ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by positivity) hmlow 3
    have hsq : F m ≤ (3 * T + 16 * T ^ 2 / (K + 1)) ^ 2 / (m : ℝ) ^ 3 := by
      simp only [hF]
      have := pow_le_pow_left₀ (norm_nonneg _) hB 2
      rw [div_pow, hmq] at this
      exact this
    have hnum : (3 * T + 16 * T ^ 2 / (K + 1)) ^ 2
        ≤ 18 * T ^ 2 + 512 * T ^ 4 * (1 / (((g m : ℤ) : ℝ) ^ 2 + 1)) := by
      have hK1 : ((g m : ℤ) : ℝ) ^ 2 + 1 ≤ (K + 1) ^ 2 := by
        have : ((g m : ℤ) : ℝ) ^ 2 = K ^ 2 := by rw [hK, sq_abs]
        rw [this]; nlinarith
      have hA : (16 * T ^ 2 / (K + 1)) ^ 2 ≤ 256 * T ^ 4 * (1 / (((g m : ℤ) : ℝ) ^ 2 + 1)) := by
        rw [div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have : (16 * T ^ 2) ^ 2 = 256 * T ^ 4 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hK1 (by positivity)
      nlinarith [sq_nonneg (3 * T - 16 * T ^ 2 / (K + 1))]
    calc F m ≤ (3 * T + 16 * T ^ 2 / (K + 1)) ^ 2 / (m : ℝ) ^ 3 := hsq
      _ ≤ (18 * T ^ 2 + 512 * T ^ 4 * (1 / (((g m : ℤ) : ℝ) ^ 2 + 1))) / (E1 / 2) ^ 3 :=
          div_le_div₀ (by positivity) hnum (by positivity) hm3
      _ = 8 / E1 ^ 3 * (18 * T ^ 2 + 512 * T ^ 4 * (1 / (((g m : ℤ) : ℝ) ^ 2 + 1))) := by
          field_simp; ring
  -- counting
  have hcard : (rel.card : ℝ) ≤ Real.exp (s + 1) + 2 := by
    have := card_le_of_Ico rel (E1 - 1) (Real.exp (s + 1)) (by linarith)
      (by have : E1 ≤ Real.exp (s + 1) := Real.exp_le_exp.mpr (by linarith); linarith)
      (fun m hm => by rw [hrel, Finset.mem_filter] at hm; exact hm.2)
    linarith
  have hfib : ∀ k : ℤ, (((rel.filter (fun m => g m = k)).card : ℕ) : ℝ) ≤ 2 * Real.exp (s + 1) / T + 1 := by
    intro k
    set fib := rel.filter (fun m => g m = k) with hfibdef
    rcases fib.eq_empty_or_nonempty with he | ⟨m₁, hm₁⟩
    · rw [he, Finset.card_empty]; push_cast; positivity
    set a := Real.exp (s + (k : ℝ) / T) with ha
    set b := Real.exp (s + ((k : ℝ) + 1) / T) with hb
    have hmem : ∀ m ∈ fib, a ≤ (m : ℝ) ∧ (m : ℝ) < b := by
      intro m hm
      rw [hfibdef, Finset.mem_filter, hrel, Finset.mem_filter] at hm
      obtain ⟨⟨_, hml, _⟩, hgk⟩ := hm
      have hm0 : (0 : ℝ) < m := by linarith
      have hk1 := Int.floor_le (T * (Real.log m - s))
      have hk2 := Int.lt_floor_add_one (T * (Real.log m - s))
      simp only [hg] at hgk
      rw [hgk] at hk1 hk2
      constructor
      · rw [ha, ← Real.exp_log hm0]
        apply Real.exp_le_exp.mpr
        have : (k : ℝ) / T ≤ Real.log m - s := by rw [div_le_iff₀ hT0]; linarith
        linarith
      · rw [hb, ← Real.exp_log hm0]
        apply Real.exp_lt_exp.mpr
        have : Real.log m - s < ((k : ℝ) + 1) / T := by rw [lt_div_iff₀ hT0]; linarith
        linarith
    have hab : a ≤ b := Real.exp_le_exp.mpr (by
      have : (k : ℝ) / T ≤ ((k : ℝ) + 1) / T := by
        apply div_le_div_of_nonneg_right _ hT0.le; linarith
      linarith)
    have hc := card_le_of_Ico fib a b (Real.exp_pos _).le hab hmem
    -- `b − a ≤ 2e^{s+1}/T`
    have hm₁' := hmem m₁ hm₁
    have hm₁rel : m₁ ∈ rel := (Finset.mem_filter.mp hm₁).1
    rw [hrel, Finset.mem_filter] at hm₁rel
    have haE : a ≤ Real.exp (s + 1) := by linarith [hm₁'.1, hm₁rel.2.2]
    have hbexp : b = a * Real.exp (1 / T) := by
      rw [ha, hb, ← Real.exp_add]; congr 1; field_simp; ring
    have hexp : Real.exp (1 / T) ≤ 1 + 2 / T := by
      have h1 : Real.exp (1 / T) ≤ 1 / (1 - 1 / T) :=
        Real.exp_bound_div_one_sub_of_interval (by positivity)
          (by rw [div_lt_one hT0]; linarith)
      have h2 : 1 / (1 - 1 / T) ≤ 1 + 2 / T := by
        rw [div_le_iff₀ (by rw [sub_pos, div_lt_one hT0]; linarith)]
        have : 0 < 1 / T := by positivity
        have h3 : 1 / T ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hT0 (by norm_num)]; linarith
        have e : (1 + 2 / T) * (1 - 1 / T) = 1 + 1 / T - 2 * (1 / T) ^ 2 := by ring
        rw [e]; nlinarith
      linarith
    have hba : b - a ≤ 2 * Real.exp (s + 1) / T := by
      rw [hbexp]
      have : a * Real.exp (1 / T) - a ≤ a * (2 / T) := by
        have := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (s + (k : ℝ) / T)).le
        rw [← ha] at this; linarith
      calc a * Real.exp (1 / T) - a ≤ a * (2 / T) := this
        _ ≤ Real.exp (s + 1) * (2 / T) := mul_le_mul_of_nonneg_right haE (by positivity)
        _ = 2 * Real.exp (s + 1) / T := by ring
    linarith
  have hweighted : ∑ m ∈ rel, 1 / (((g m : ℤ) : ℝ) ^ 2 + 1)
      ≤ (2 * Real.exp (s + 1) / T + 1) * Cz := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := rel.image g)
      (fun m hm => Finset.mem_image_of_mem g hm)]
    have hB0 : 0 ≤ 2 * Real.exp (s + 1) / T + 1 := by positivity
    calc ∑ k ∈ rel.image g, ∑ m ∈ rel.filter (fun m => g m = k), 1 / (((g m : ℤ) : ℝ) ^ 2 + 1)
        = ∑ k ∈ rel.image g, (((rel.filter (fun m => g m = k)).card : ℕ) : ℝ) * (1 / ((k : ℝ) ^ 2 + 1)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_congr rfl (fun m hm => by
            rw [(Finset.mem_filter.mp hm).2]), Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ rel.image g, (2 * Real.exp (s + 1) / T + 1) * (1 / ((k : ℝ) ^ 2 + 1)) :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hfib k) (by positivity)
      _ = (2 * Real.exp (s + 1) / T + 1) * ∑ k ∈ rel.image g, 1 / ((k : ℝ) ^ 2 + 1) := by
          rw [Finset.mul_sum]
      _ ≤ (2 * Real.exp (s + 1) / T + 1) * Cz :=
          mul_le_mul_of_nonneg_left (summable_Cz.sum_le_tsum _ (fun k _ => by positivity)) hB0
  -- assemble
  rw [show (∑ m ∈ Finset.Ioc 0 N, ‖wmod T s (m + 1) - wmod T s m‖ ^ 2) = ∑ m ∈ Finset.Ioc 0 N, F m from rfl,
    hrelsum]
  have hc8 : 0 ≤ 8 / E1 ^ 3 := by positivity
  calc ∑ m ∈ rel, F m
      ≤ ∑ m ∈ rel, 8 / E1 ^ 3 * (18 * T ^ 2 + 512 * T ^ 4 * (1 / (((g m : ℤ) : ℝ) ^ 2 + 1))) :=
        Finset.sum_le_sum hterm
    _ = 8 / E1 ^ 3 * (18 * T ^ 2 * (rel.card : ℝ)
          + 512 * T ^ 4 * ∑ m ∈ rel, 1 / (((g m : ℤ) : ℝ) ^ 2 + 1)) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ 8 / E1 ^ 3 * (18 * T ^ 2 * (Real.exp (s + 1) + 2)
          + 512 * T ^ 4 * ((2 * Real.exp (s + 1) / T + 1) * Cz)) := by
        apply mul_le_mul_of_nonneg_left _ hc8
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcard (by positivity)
        · exact mul_le_mul_of_nonneg_left hweighted (by positivity)

end K6
end LemmaK
end ZetaShell

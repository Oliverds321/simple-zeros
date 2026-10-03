/-
Node K6 (track K) — thm:zeta-G (l.488–502) with lem:zeta-Dprime (l.514–527), abstract: under GramFamily N R k_ψ and
LocalCert k_ψ W c (c > 0, |k_ψ| ≤ 1), for every m ≥ K with Φ_m(A) < m,
"liminf s₁/N ≥ (H − (B/A)τ)/(1 − B/m)", H = 2 − R — in ε-form.
Proof: K4 + (AF3, AF4, window) give s₁ ≥ (2 − R)N + tr Ψ(M°) − o(N); K5 at c′ < c; solve for s₁; c′ ↑ c
(continuity of stabConst in c, node K6a).
Deps: K4, K5, K6a; trunk `eps_form_of_isLittleO` (Zeta23/Assembly.lean:488).
-/
import ZetaS.Interfaces
import Zeta23.Assembly
import ZetaS.KSide.K4_StabFixedT
import ZetaS.KSide.K5_TransferMcirc
import ZetaS.KSide.K6a_StabConstCont

open Filter Asymptotics Topology

namespace ZetaS

theorem thmG_abstract {N : ℝ → ℝ} {R : ℝ} {kψ : ℝ → ℝ} (Fm : GramFamily N R kψ)
    (hk1 : ∀ t, |kψ t| ≤ 1) {K : ℕ} (W : LocalWeights K) {c : ℝ} (hc : 0 < c)
    (hLI : LocalCert kψ W c) {m : ℕ} (hKm : K ≤ m) (hBm : PhiM m (c * ((m : ℝ) - K + 1)) < m) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (stabConst (2 - R) K W.nu c m - ε) * N T ≤ ((Fm.G T).s1 : ℝ) := by
  intro ε hε
  have hK2 : 2 ≤ K := W.two_le
  have hm : 2 ≤ m := le_trans hK2 hKm
  have hKmR : (K : ℝ) ≤ m := by exact_mod_cast hKm
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  -- (1) choose c′ < c with stabConst(c′) > stabConst(c) − ε/2 and Φ_m(A′) < m (K6a)
  have hcont := stabConst_continuousAt (H := 2 - R) (ν := W.nu) hK2 hKm hc hBm
  have hBc : ContinuousAt (fun c' : ℝ => PhiM m (c' * ((m : ℝ) - K + 1))) c :=
    (K6aux.PhiM_continuous hm).continuousAt.comp (by fun_prop)
  have h1 : ∀ᶠ c' in 𝓝 c, stabConst (2 - R) K W.nu c m - ε / 2 < stabConst (2 - R) K W.nu c' m :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ c' in 𝓝 c, PhiM m (c' * ((m : ℝ) - K + 1)) < m := hBc.eventually (gt_mem_nhds hBm)
  have h3 : ∀ᶠ c' in 𝓝 c, 0 < c' := lt_mem_nhds hc
  have hev : ∀ᶠ c' in 𝓝[<] c, (stabConst (2 - R) K W.nu c m - ε / 2 < stabConst (2 - R) K W.nu c' m ∧
      PhiM m (c' * ((m : ℝ) - K + 1)) < m ∧ 0 < c') ∧ c' ∈ Set.Iio c :=
    ((h1.and (h2.and h3)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨c', ⟨hc1, hc2, hc3⟩, hc4⟩ := hev.exists
  rw [Set.mem_Iio] at hc4
  -- (2) K5 at c′, K4, and the family inputs
  obtain ⟨r, hr, hK5⟩ := transfer_Mcirc Fm hk1 W hLI hc3 hc4 hKm
  have hS : stabConst (2 - R) K W.nu c' m
      = ((2 - R) - PhiM m (c' * ((m : ℝ) - K + 1)) / (c' * ((m : ℝ) - K + 1)) * (W.nu * ((m : ℝ) - K + 1) / m))
        / (1 - PhiM m (c' * ((m : ℝ) - K + 1)) / m) := rfl
  set B' := PhiM m (c' * ((m : ℝ) - K + 1)) with hB'
  set C := B' / (c' * ((m : ℝ) - K + 1)) * (W.nu * ((m : ℝ) - K + 1) / m) with hC
  have hβ : 0 < 1 - B' / m := by
    have : B' / m < 1 := by rw [div_lt_one hm0]; exact hc2
    linarith
  set err0 : ℝ → ℝ := fun T => -4 * (RHLinalg.rtrace (Fm.G T).Gt - N T) + 2 * (((Fm.G T).Nw : ℝ) - N T)
    + (RHLinalg.frobSq (Fm.G T).Gt - R * N T) + r T with herr0
  have herr0o : err0 =o[atTop] N :=
    (((Fm.trace.const_mul_left (-4)).add (Fm.window.const_mul_left 2)).add Fm.frob).add hr
  have hmain : ∀ᶠ T in atTop, stabConst (2 - R) K W.nu c' m * N T - err0 T / (1 - B' / m)
      ≤ ((Fm.G T).s1 : ℝ) := by
    filter_upwards [hK5] with T hT
    have h4 := stab_fixedT (Fm.G T)
    have key : ((2 - R) - C) * N T - err0 T ≤ (1 - B' / m) * ((Fm.G T).s1 : ℝ) := by
      simp only [herr0]
      have : B' / m * ((Fm.G T).s1 : ℝ) = B' / ↑m * ↑(Fm.G T).s1 := rfl
      nlinarith
    rw [hS]
    rw [div_mul_eq_mul_div, ← sub_div, div_le_iff₀ hβ]
    linarith
  have herr : (fun T => err0 T / (1 - B' / m)) =o[atTop] N := by
    simpa only [div_eq_inv_mul] using herr0o.const_mul_left (1 - B' / m)⁻¹
  obtain ⟨T₀, hT₀⟩ := Zeta23.Assembly.eps_form_of_isLittleO hmain Fm.N_nonneg herr (ε / 2) (half_pos hε)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp Fm.N_nonneg
  refine ⟨max T₀ T₁, fun T hT => ?_⟩
  have hN := hT₁ T (le_trans (le_max_right _ _) hT)
  have h := hT₀ T (le_trans (le_max_left _ _) hT)
  have : (stabConst (2 - R) K W.nu c m - ε) * N T ≤ (stabConst (2 - R) K W.nu c' m - ε / 2) * N T :=
    mul_le_mul_of_nonneg_right (by linarith) hN
  linarith

end ZetaS

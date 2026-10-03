/-
S1_FromZ (L7_5b, 1 Oct 2026): Theorem S, step 1 (`S1_ring_to_zeros`, L7_10's statement, verbatim) DERIVED from
Proposition Z (`propZ_W`, proved; used in the dominated form `propZ_W_dom`), Lemma 5a (`plancherel_majorant`, proved)
and A⋆ (`AstarCorrStmt` = L7_6's `ring_le_primitive_corr`, open), with the remaining inputs of S1_Leaves.lean.
-/
import ZetaShell.ShellS.S1_Leaves

noncomputable section
open MeasureTheory

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- `‖P_χ(β)‖ ≤ T Σ_{n ∈ (e^{s−1}, N(s)], n not prime} Λ(n) n^{−1/2}`. -/
theorem PPart_norm_le {r : ℕ} (χ : DirichletCharacter ℂ r) (T κ : ℝ) (hT : 0 ≤ T) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ) (s β : ℝ) :
    ‖PPart χ T κ Ξ s β‖ ≤ T * ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter
      (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold PPart
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, ← Finset.filter_filter]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro n _
  have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  rw [norm_mul, norm_mul, norm_mul, norm_eA, mul_one, Complex.norm_real, Real.norm_of_nonneg hΛ]
  split_ifs with hn
  · have hAs : ‖As T κ Ξ s n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * T := by
      unfold As
      have h1 : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1,
        Real.norm_of_nonneg (hΞ.nonneg _), DT_eq_DTf]
      have h2 := ZetaShell.DTFacts.norm_DTf_le hT (s - Real.log n)
      have h3 := hΞ.le_one ((Real.log n - s) / κ)
      have h4 : 0 ≤ ‖ZetaShell.DTFacts.DTf T (s - Real.log n)‖ := norm_nonneg _
      calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖ZetaShell.DTFacts.DTf T (s - Real.log n)‖ * Ξ ((Real.log n - s) / κ)
          ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * ‖ZetaShell.DTFacts.DTf T (s - Real.log n)‖ * 1 := by gcongr
        _ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) * T := by rw [mul_one]; gcongr
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ n‖ * ‖As T κ Ξ s n‖
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * ((n : ℝ) ^ (-(1 / 2 : ℝ)) * T) := by
          gcongr
      _ = T * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
  · have h0 : As T κ Ξ s n = 0 := by
      apply As_eq_zero_outside T κ hκ Ξ hΞ s
      intro hmem
      apply hn
      have := hmem.1
      calc Real.exp (s - 1) ≤ Real.exp (s - κ) := Real.exp_le_exp.mpr (by linarith)
        _ < n := this
    rw [h0, norm_zero, mul_zero]

/-- one primitive character's ring integral: `≤ ∫ ‖S_χ‖² Φ(β/Δ) + 2Δ(T Cp)²` (Lemma 5a and the prime-power bound). -/
theorem ring_piece_le (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c) (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (Cp : ℝ) (hCp : ∀ s : ℝ, ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter
      (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Cp)
    (Qn : ℕ) (s₀ T Δ s : ℝ) (hs₀ : 3 ≤ s₀) (hT : 2 ≤ T) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hs : |s - s₀| ≤ 1)
    (hQ : (Qn : ℝ) ≤ Real.exp (s - 1))
    (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (S : Set ℝ) (hS : S ⊆ Set.Icc (-Δ) Δ) :
    (∫ β in S, ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2)
      ≤ (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)) + 2 * Δ * (T * Cp) ^ 2 := by
  obtain ⟨F, a, g, hg, hgs, hSch, -⟩ := ZB_Schi_form κ hκ hκ1 Ξ hΞ f hf s₀ T Δ s hs₀ hT hΔ hΔ1 hs r χ hχ
  obtain ⟨-, hmaj, -⟩ := plancherel_majorant f hf c hc0 hc F a g hg hgs Δ hΔ
  have hfun : (fun β => Schi χ T κ Ξ s β)
      = fun β => ∑ y ∈ F, a y * eA (y * β) + ∫ y, g y * eA (y * β) := funext hSch
  have hcont : Continuous (fun β => Schi χ T κ Ξ s β) := by rw [hfun]; exact continuous_S F a g hg hgs
  have hmaj' : (∫ β in Set.Icc (-Δ) Δ, ‖Schi χ T κ Ξ s β‖ ^ 2)
      ≤ ∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ) := by
    simp only [hSch]; exact hmaj
  have hT0 : 0 ≤ T := by linarith
  have hpi : (2 * Real.pi)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith [Real.pi_gt_three]
  have hpi0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hpt : ∀ β, ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β
      - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2 ≤ ‖Schi χ T κ Ξ s β‖ ^ 2 + (T * Cp) ^ 2 := by
    intro β
    rw [twist_sub_model Qn T κ hκ hκ1 Ξ hΞ s hQ r χ β]
    have hP : ‖PPart χ T κ Ξ s β‖ ≤ T * Cp :=
      (PPart_norm_le χ T κ hT0 hκ hκ1 Ξ hΞ s β).trans (mul_le_mul_of_nonneg_left (hCp s) hT0)
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hpi0]
    have h1 : ‖Schi χ T κ Ξ s β - PPart χ T κ Ξ s β‖ ≤ ‖Schi χ T κ Ξ s β‖ + ‖PPart χ T κ Ξ s β‖ := norm_sub_le _ _
    have h2 : 0 ≤ ‖Schi χ T κ Ξ s β - PPart χ T κ Ξ s β‖ := norm_nonneg _
    have h3 : 0 ≤ ‖PPart χ T κ Ξ s β‖ := norm_nonneg _
    have h4 : 0 ≤ ‖Schi χ T κ Ξ s β‖ := norm_nonneg _
    have h5 : (2 * Real.pi)⁻¹ * ‖Schi χ T κ Ξ s β - PPart χ T κ Ξ s β‖
        ≤ 1 / 2 * (‖Schi χ T κ Ξ s β‖ + ‖PPart χ T κ Ξ s β‖) :=
      mul_le_mul hpi h1 h2 (by norm_num)
    have h6 : 0 ≤ (2 * Real.pi)⁻¹ * ‖Schi χ T κ Ξ s β - PPart χ T κ Ξ s β‖ := mul_nonneg hpi0 h2
    have h7 := pow_le_pow_left₀ h6 h5 2
    have h8 : ‖PPart χ T κ Ξ s β‖ ^ 2 ≤ (T * Cp) ^ 2 := pow_le_pow_left₀ h3 hP 2
    nlinarith [sq_nonneg (‖Schi χ T κ Ξ s β‖ - ‖PPart χ T κ Ξ s β‖)]
  have hIcc : IntegrableOn (fun β => ‖Schi χ T κ Ξ s β‖ ^ 2) (Set.Icc (-Δ) Δ) :=
    (hcont.norm.pow 2).continuousOn.integrableOn_Icc
  have hSfin : volume S ≠ ⊤ := ((measure_mono hS).trans_lt measure_Icc_lt_top).ne
  have hSi : IntegrableOn (fun β => ‖Schi χ T κ Ξ s β‖ ^ 2) S := hIcc.mono_set hS
  have hCi : IntegrableOn (fun _ : ℝ => (T * Cp) ^ 2) S := integrableOn_const hSfin
  have hvol : volume.real S ≤ 2 * Δ := by
    calc volume.real S ≤ volume.real (Set.Icc (-Δ) Δ) := measureReal_mono hS measure_Icc_lt_top.ne
      _ = 2 * Δ := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  calc (∫ β in S, ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β
          - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2)
      ≤ ∫ β in S, (‖Schi χ T κ Ξ s β‖ ^ 2 + (T * Cp) ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun β => sq_nonneg _)
          (Integrable.add hSi hCi : Integrable (fun β => ‖Schi χ T κ Ξ s β‖ ^ 2 + (T * Cp) ^ 2) (volume.restrict S))
          (Filter.Eventually.of_forall hpt)
    _ = (∫ β in S, ‖Schi χ T κ Ξ s β‖ ^ 2) + volume.real S * (T * Cp) ^ 2 := by
        rw [integral_add hSi hCi, setIntegral_const, smul_eq_mul]
    _ ≤ (∫ β in Set.Icc (-Δ) Δ, ‖Schi χ T κ Ξ s β‖ ^ 2) + 2 * Δ * (T * Cp) ^ 2 := by
        exact add_le_add (setIntegral_mono_set hIcc (Filter.Eventually.of_forall fun β => sq_nonneg _)
          (Filter.Eventually.of_forall hS)) (mul_le_mul_of_nonneg_right hvol (sq_nonneg _))
    _ ≤ (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)) + 2 * Δ * (T * Cp) ^ 2 := by gcongr

theorem primChars_card_le (r : ℕ) [NeZero r] : ((primChars r).card : ℝ) ≤ (Nat.totient r : ℝ) := by
  have h1 : (primChars r).card ≤ Fintype.card (DirichletCharacter ℂ r) := Finset.card_le_univ _
  have h2 : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
    rw [← Nat.card_eq_fintype_card]; exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
  rw [h2] at h1
  exact_mod_cast h1

theorem primChars_eq (r : ℕ) : ZetaQ.primitiveChars r = primChars r := rfl

/-- **S1 pointwise** (fixed `s`, `|s − s₀| ≤ 1`): A⋆ with `Cμ = D(log K + 1) − log K`, `U = CU·T`, `M = M_s`, then
each primitive character's ring integral by `ring_piece_le`, and `(r/φ(r)) #{χ} ≤ r`. -/
theorem ring_pointwise (hAst : AstarCorrStmt) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ) (hΞ : NearCutoff Ξ)
    (f : ℝ → ℝ) (hf : TestFn f) (c : ℝ) (hc0 : 0 < c) (hc : ∀ η ∈ Set.Icc (-1 : ℝ) 1, c ≤ ‖fhat f η‖ ^ 2)
    (Cp : ℝ) (hCp : ∀ s : ℝ, ∑ n ∈ (Finset.Ioc 0 (Nnear s)).filter
      (fun n : ℕ => ¬ n.Prime ∧ Real.exp (s - 1) < (n : ℝ)),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Cp)
    (D : ℝ) (hD1 : 1 ≤ D) (hDw : ∀ (R1 : ℕ) (K : ℝ), 1 ≤ K → ∀ y : ℝ, 0 < y →
      ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ D * (Real.log K + 1))
    (CU : ℝ) (hMU : ∀ T : ℝ, 2 ≤ T → ∀ s : ℝ, Continuous (Mmod T κ Ξ s) ∧
      (∫ β in (-(1 / 2 : ℝ))..(1 / 2), ‖Mmod T κ Ξ s β‖ ^ 2) ≤ CU * T)
    (Qn : ℕ) (hQ1 : 1 ≤ (Qn : ℝ)) (T : ℝ) (hT : 2 ≤ T) (K ε s₀ : ℝ) (hK1 : 1 ≤ K)
    (hs₀ : Real.log Qn + 3 ≤ s₀)
    (hRQ : 2 * K * (R1S Qn ε s₀ : ℝ) ≤ Qn) (hKQ : K / Qn ≤ 1)
    (s : ℝ) (hs : |s - s₀| ≤ 1) :
    RingS Qn T κ Ξ K ε s₀ s ≤ 2 * (D * (Real.log K + 1)) *
      (∑ r ∈ Finset.Icc 1 (R1S Qn ε s₀), ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r,
        (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn)))))
      + 2 * (D * (Real.log K + 1)) * (2 * T ^ 2 * Cp ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn + CU * T) := by
  set R1 := R1S Qn ε s₀ with hR1def
  set Cμ := D * (Real.log K + 1) - Real.log K with hCμdef
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hCμ0 : 0 ≤ Cμ := by rw [hCμdef]; nlinarith
  have hLK : Real.log K + Cμ = D * (Real.log K + 1) := by rw [hCμdef]; ring
  have hQpos : (0 : ℝ) < Qn := by linarith
  have hlogQ : 0 ≤ Real.log Qn := Real.log_nonneg hQ1
  have hs₀3 : 3 ≤ s₀ := by linarith
  have hQs : (Qn : ℝ) ≤ Real.exp (s - 1) := by
    have h1 : Real.log Qn ≤ s - 1 := by have := (abs_le.mp hs).1; linarith
    calc (Qn : ℝ) = Real.exp (Real.log Qn) := (Real.exp_log hQpos).symm
      _ ≤ Real.exp (s - 1) := Real.exp_le_exp.mpr h1
  obtain ⟨hMc, hU⟩ := hMU T hT s
  have hsupp : ∀ n ∈ Finset.Ioc 0 (Nnear s), aNearP Qn T κ Ξ s n ≠ 0 →
      ∀ p : ℕ, p.Prime → p ∣ n → Qn < p := by
    intro n _ hn p hp hpn
    unfold aNearP at hn
    split_ifs at hn with h
    · obtain ⟨hnp, hQn⟩ := h
      have hpn' : p = n := (Nat.prime_dvd_prime_iff_eq hp hnp).mp hpn
      subst hpn'; exact_mod_cast hQn
    · exact absurd rfl hn
  have hmult : ∀ y : ℝ, 0 < y →
      ∑ m ∈ (Finset.Icc 1 R1).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) < K * y),
        ((ArithmeticFunction.moebius m : ℝ) ^ 2 / (Nat.totient m : ℝ)) ≤ Real.log K + Cμ :=
    fun y hy => (hDw R1 K hK1 y hy).trans hLK.symm.le
  have hA := hAst Qn R1 (Nnear s) K Cμ (CU * T) (aNearP Qn T κ Ξ s) (Mmod T κ Ξ s) hK1 hRQ hCμ0 hsupp hmult hMc hU
  have hRing : RingS Qn T κ Ξ K ε s₀ s = TrackF.ringMass Qn R1 (Nnear s) K (aNearP Qn T κ Ξ s) := rfl
  rw [hRing]
  refine hA.trans ?_
  rw [hLK]
  have hL0 : 0 ≤ 2 * (D * (Real.log K + 1)) := by positivity
  have hper : ∀ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars r,
        (∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Qn) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Qn)},
          ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2)
      ≤ ((r : ℝ) / (Nat.totient r : ℝ)) * (∑ χ ∈ primChars r,
          (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn)))))
        + 2 * K * (T * Cp) ^ 2 / Qn := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    haveI : NeZero r := ⟨by omega⟩
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
    have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hφpos : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr1
    set Δ := K / ((r : ℝ) * Qn) with hΔdef
    have hKpos : 0 < K := by linarith
    have hΔpos : 0 < Δ := by positivity
    have hΔ1 : Δ ≤ 1 := by
      calc Δ ≤ K / Qn := by
            rw [hΔdef]; apply div_le_div_of_nonneg_left hKpos.le hQpos
            nlinarith
        _ ≤ 1 := hKQ
    have hsub : {β : ℝ | 1 / ((R1 : ℝ) * Qn) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Qn)} ⊆ Set.Icc (-Δ) Δ :=
      fun β hβ => Set.mem_Icc.mpr (abs_le.mp hβ.2)
    have hpiece : ∀ χ ∈ ZetaQ.primitiveChars r,
        (∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Qn) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Qn)},
          ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2)
        ≤ (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)) + 2 * Δ * (T * Cp) ^ 2 := by
      intro χ hχ
      have hχp : χ.IsPrimitive := ZetaQ.mem_primitiveChars.mp hχ
      exact ring_piece_le κ hκ hκ1 Ξ hΞ f hf c hc0 hc Cp hCp Qn s₀ T Δ s hs₀3 hT hΔpos hΔ1 hs hQs r χ hχp _ hsub
    have hsum := Finset.sum_le_sum hpiece
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
    have hcard := primChars_card_le r
    have hratio : (r : ℝ) / (Nat.totient r : ℝ) * ((primChars r).card : ℝ) ≤ r := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hφpos]
      exact mul_le_mul_of_nonneg_left hcard hrpos.le
    have hD2 : 0 ≤ 2 * Δ * (T * Cp) ^ 2 := by positivity
    have hrΔ : (r : ℝ) * (2 * Δ * (T * Cp) ^ 2) = 2 * K * (T * Cp) ^ 2 / Qn := by
      rw [hΔdef]; field_simp
    calc ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ ZetaQ.primitiveChars r,
          (∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Qn) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Qn)},
            ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2)
        ≤ ((r : ℝ) / (Nat.totient r : ℝ)) * ((∑ χ ∈ ZetaQ.primitiveChars r,
            (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)))
            + ((ZetaQ.primitiveChars r).card : ℝ) * (2 * Δ * (T * Cp) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((r : ℝ) / (Nat.totient r : ℝ)) * (∑ χ ∈ primChars r,
            (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)))
          + ((r : ℝ) / (Nat.totient r : ℝ) * ((primChars r).card : ℝ)) * (2 * Δ * (T * Cp) ^ 2) := by
          rw [primChars_eq]; ring
      _ ≤ ((r : ℝ) / (Nat.totient r : ℝ)) * (∑ χ ∈ primChars r,
            (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / Δ)))
          + (r : ℝ) * (2 * Δ * (T * Cp) ^ 2) := by gcongr
      _ = _ := by rw [hrΔ]
  have hsumr := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hsumr
  have hTC : (T * Cp) ^ 2 = T ^ 2 * Cp ^ 2 := by ring
  calc 2 * (D * (Real.log K + 1)) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ ZetaQ.primitiveChars r,
            (∫ β in {β : ℝ | 1 / ((R1 : ℝ) * Qn) ≤ |β| ∧ |β| ≤ K / ((r : ℝ) * Qn)},
              ‖TrackF.twistSum (Nnear s) (aNearP Qn T κ Ξ s) χ β - (if r = 1 then Mmod T κ Ξ s β else 0)‖ ^ 2))
        + 2 * (D * (Real.log K + 1)) * (CU * T)
      ≤ 2 * (D * (Real.log K + 1)) * ((∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          (∑ χ ∈ primChars r, (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn))))))
          + (R1 : ℝ) * (2 * K * (T * Cp) ^ 2 / Qn))
        + 2 * (D * (Real.log K + 1)) * (CU * T) := by gcongr
    _ = _ := by rw [hTC]; ring

theorem RingS_nonneg (Qn : ℕ) (T κ : ℝ) (Ξ : ℝ → ℝ) (K ε s₀ s : ℝ) : 0 ≤ RingS Qn T κ Ξ K ε s₀ s := by
  unfold RingS TrackF.ringMass
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

set_option maxHeartbeats 2000000 in
/-- **S1 (Theorem S, step 1) derived from Proposition Z and A⋆.** The conclusion is L7_10's `S1_ring_to_zeros`,
verbatim; A⋆ (`ring_le_primitive_corr`, open at L7_6) enters as the explicit hypothesis `hAst`. -/
theorem S1_ring_to_zeros_of_astar (hAst : AstarCorrStmt) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (Ξ : ℝ → ℝ)
    (hΞ : NearCutoff Ξ) (A : ℕ) (hA : 2 ≤ A)
    (r0 ε0 : ℝ) (hr0 : 3 ≤ r0) (hε0 : 0 < ε0) (αp B : ℝ) (hα1 : 1 < αp) (hα2 : αp < 2) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ Qn : ℕ in Filter.atTop, ∀ K ε s₀ : ℝ, SRange αp B Qn K ε s₀ →
      ∀ W : ℝ → ℝ, AvgWeight W →
        Integrable (fun s => W (s - s₀) * RingS Qn (twin Qn r0 ε0) κ Ξ K ε s₀ s) ∧
        (∫ s, W (s - s₀) * RingS Qn (twin Qn r0 ε0) κ Ξ K ε s₀ s)
          ≤ C * normCA W A * (Real.log K + 2) *
            (twin Qn r0 ε0 * zeroPairSum Qn (twin Qn r0 ε0) K ε s₀ A 3
              + famErrSum Qn (twin Qn r0 ε0) K ε s₀
              + (twin Qn r0 ε0 ^ 2 * K * (R1S Qn ε s₀ : ℝ) / Qn + twin Qn r0 ε0)) := by
  obtain ⟨f, c, hf, hc0, hc⟩ := exists_testFn
  obtain ⟨C₀, hC₀, hZ⟩ := propZ_W_dom κ hκ hκ1 Ξ hΞ f hf c hc0 hc A 3 hA (by norm_num)
  obtain ⟨D, hD1, hDw⟩ := musq_window
  obtain ⟨Cp, hCp0, hCp⟩ := pp_window
  obtain ⟨CU, hCU0, hMU⟩ := Mmod_props κ hκ hκ1 Ξ hΞ
  refine ⟨2 * D * (C₀ + 4 * Cp ^ 2 + 2 * CU), by positivity, ?_⟩
  filter_upwards [S1_eventually r0 ε0 hr0 hε0 αp B hα2 hB] with Qn hQn
  obtain ⟨hT2, hQ1, hev⟩ := hQn
  intro K ε s₀ hR W hW
  obtain ⟨hRQ, hR1e, hKQ⟩ := hev K ε s₀ hR
  set T := twin Qn r0 ε0 with hTdef
  set R1 := R1S Qn ε s₀ with hR1def
  set N := normCA W A with hNdef
  have hK1 : (1 : ℝ) ≤ K := by linarith [hR.K_ge]
  have hKpos : 0 < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hQpos : (0 : ℝ) < Qn := by linarith
  have hlogQ : 0 ≤ Real.log Qn := Real.log_nonneg hQ1
  have hs₀ : 3 ≤ s₀ := by linarith [hR.s_ge]
  have hT0 : 0 ≤ T := by linarith
  have hN0 : 0 ≤ N := normCA_nonneg W A
  set L := 2 * (D * (Real.log K + 1)) with hLdef
  have hL0 : 0 ≤ L := by positivity
  set zp : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r χ =>
    if h : r = 0 then 0 else haveI : NeZero r := ⟨h⟩; ∑' p, pairTerm χ T (muR Qn K s₀ r) s₀ A 3 p with hzp
  have hZ' : ∀ (r : ℕ) (χ : DirichletCharacter ℂ r), ∃ H : ℝ → ℝ, Integrable H ∧
      (r ∈ Finset.Icc 1 R1 → χ ∈ primChars r →
        (∀ s, W (s - s₀) * (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn)))) ≤ H s) ∧
        (∫ s, H s) ≤ C₀ * N * (T * zp r χ + EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn)))) := by
    intro r χ
    by_cases h : r ∈ Finset.Icc 1 R1 ∧ χ ∈ primChars r
    · obtain ⟨hr, hχ⟩ := h
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hr0 : r ≠ 0 := by omega
      haveI : NeZero r := ⟨hr0⟩
      have hχp : χ.IsPrimitive := ZetaQ.mem_primitiveChars.mp hχ
      have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have hΔpos : 0 < K / ((r : ℝ) * Qn) := by positivity
      have hΔ1 : K / ((r : ℝ) * Qn) ≤ 1 := by
        calc K / ((r : ℝ) * Qn) ≤ K / Qn := by
              apply div_le_div_of_nonneg_left hKpos.le hQpos
              nlinarith
          _ ≤ 1 := hKQ
      have hrexp : (r : ℝ) ≤ Real.exp s₀ := by
        have : (r : ℝ) ≤ R1 := by exact_mod_cast (Finset.mem_Icc.mp hr).2
        linarith
      obtain ⟨_, H, hHi, hHle, hHint⟩ := hZ W hW s₀ T (K / ((r : ℝ) * Qn)) hs₀ hT2 hΔpos hΔ1 r χ hχp hrexp
      refine ⟨H, hHi, fun _ _ => ⟨hHle, ?_⟩⟩
      have hmu : K / ((r : ℝ) * Qn) * Real.exp s₀ = muR Qn K s₀ r := by
        unfold muR; field_simp
      have hzpr : zp r χ = ∑' p, PropZ.pairTerm χ T (K / ((r : ℝ) * Qn) * Real.exp s₀) s₀ A 3 p := by
        rw [hzp, hmu]
        simp only [dif_neg hr0]
        rfl
      rw [hzpr]; exact hHint
    · exact ⟨0, integrable_zero _ _ _, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose H hHi hH using hZ'
  have hWsupp : ∀ s, W (s - s₀) ≠ 0 → |s - s₀| ≤ 1 := by
    intro s h0
    have h := hW.supp (subset_tsupport _ h0)
    rw [Set.mem_Ioo] at h
    exact abs_le.mpr ⟨h.1.le, h.2.le⟩
  have hWi : Integrable (fun s => W (s - s₀)) := by
    have hWc : HasCompactSupport W :=
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport W) (hW.supp.trans Set.Ioo_subset_Icc_self)
    exact (hW.smooth.continuous.integrable_of_hasCompactSupport hWc).comp_sub_right s₀
  set X := 2 * T ^ 2 * Cp ^ 2 * K * (R1 : ℝ) / Qn + CU * T with hXdef
  have hX0 : 0 ≤ X := by positivity
  set G : ℝ → ℝ := fun s => L * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ χ ∈ primChars r, H r χ s + W (s - s₀) * (L * X) with hGdef
  have hGi : Integrable G :=
    ((integrable_finsetSum _ fun r _ =>
      ((integrable_finsetSum _ fun χ _ => hHi r χ).const_mul _)).const_mul L).add (hWi.mul_const _)
  have hGint : (∫ s, G s) = L * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ χ ∈ primChars r, (∫ s, H r χ s) + (∫ s, W (s - s₀)) * (L * X) := by
    rw [hGdef, integral_add (((integrable_finsetSum _ fun r _ =>
      ((integrable_finsetSum _ fun χ _ => hHi r χ).const_mul _)).const_mul L)) (hWi.mul_const _),
      integral_const_mul, integral_finsetSum _ fun r _ => ((integrable_finsetSum _ fun χ _ => hHi r χ).const_mul _),
      integral_mul_const]
    congr 2
    apply Finset.sum_congr rfl; intro r _
    rw [integral_const_mul, integral_finsetSum _ fun χ _ => hHi r χ]
  have hHnn : ∀ r ∈ Finset.Icc 1 R1, ∀ χ ∈ primChars r, ∀ s, 0 ≤ H r χ s := fun r hr χ hχ s =>
    le_trans (mul_nonneg (hW.nonneg _) (integral_nonneg fun β =>
      mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hc0.le))) ((hH r χ hr hχ).1 s)
  have hbound : ∀ s, W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s ≤ G s := by
    intro s
    have hS2 : 0 ≤ ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, H r χ s :=
      Finset.sum_nonneg fun r hr => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun χ hχ => hHnn r hr χ hχ s)
    by_cases h0 : W (s - s₀) = 0
    · rw [h0, zero_mul, hGdef]
      simp only [h0, zero_mul, add_zero]
      exact mul_nonneg hL0 hS2
    · have hs := hWsupp s h0
      have hp := ring_pointwise hAst κ hκ hκ1 Ξ hΞ f hf c hc0 hc Cp hCp D hD1 hDw CU hMU Qn hQ1 T hT2 K ε s₀ hK1
        hR.s_ge hRQ hKQ s hs
      have hWn := hW.nonneg (s - s₀)
      have hWS : W (s - s₀) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r,
            (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn)))))
          ≤ ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, H r χ s := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro r hr
        rw [← mul_assoc, mul_comm (W (s - s₀)), mul_assoc, Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro χ hχ
        exact (hH r χ hr hχ).1 s
      calc W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s
          ≤ W (s - s₀) * (L * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r,
              (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn))))) + L * X) :=
            mul_le_mul_of_nonneg_left hp hWn
        _ = L * (W (s - s₀) * (∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r,
              (∫ β, ‖Schi χ T κ Ξ s β‖ ^ 2 * Phi f c (β / (K / ((r : ℝ) * Qn)))))) + W (s - s₀) * (L * X) := by
            ring
        _ ≤ G s := add_le_add (mul_le_mul_of_nonneg_left hWS hL0) le_rfl
  have hnn : ∀ s, 0 ≤ W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s := fun s =>
    mul_nonneg (hW.nonneg _) (RingS_nonneg _ _ _ _ _ _ _ _)
  refine ⟨hGi.mono' (ringS_aesm Qn T κ hκ hκ1 Ξ hΞ K ε s₀ W hW)
    (Filter.Eventually.of_forall fun s => by rw [Real.norm_of_nonneg (hnn s)]; exact hbound s), ?_⟩
  -- the integral
  have hWint := int_W_le W hW A s₀
  set ZS := zeroPairSum Qn T K ε s₀ A 3 with hZSdef
  set FE := famErrSum Qn T K ε s₀ with hFEdef
  have hE0 : ∀ r : ℕ, 0 ≤ EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn)) := by
    intro r; unfold EerrW
    have := Real.exp_pos s₀
    have hrr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    positivity
  have hzp0 : ∀ r ∈ Finset.Icc 1 R1, ∀ χ ∈ primChars r, 0 ≤ zp r χ := by
    intro r hr χ _
    have hr0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
    rw [hzp]; simp only [dif_neg hr0]
    haveI : NeZero r := ⟨hr0⟩
    exact tsum_nonneg fun p => pairTerm_nonneg χ T _ s₀ A 3 (by unfold muR; positivity) p
  have hZS : ZS = ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, zp r χ := rfl
  have hZS0 : 0 ≤ ZS := by
    rw [hZS]; exact Finset.sum_nonneg fun r hr => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun χ hχ => hzp0 r hr χ hχ)
  have hFE : FE = ∑ r ∈ Finset.Icc 1 R1, (r : ℝ) * EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn)) := rfl
  have hFE0 : 0 ≤ FE := by
    rw [hFE]; exact Finset.sum_nonneg fun r _ => mul_nonneg (Nat.cast_nonneg r) (hE0 r)
  have hsumH : ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, (∫ s, H r χ s)
      ≤ C₀ * N * (T * ZS + FE) := by
    have hper : ∀ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, (∫ s, H r χ s)
        ≤ C₀ * N * (T * (((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, zp r χ)
          + (r : ℝ) * EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn))) := by
      intro r hr
      have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
      haveI : NeZero r := ⟨by omega⟩
      have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
      have hφpos : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr1
      have hratio : (r : ℝ) / (Nat.totient r : ℝ) * ((primChars r).card : ℝ) ≤ r := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hφpos]
        exact mul_le_mul_of_nonneg_left (primChars_card_le r) hrpos.le
      have h1 : ∑ χ ∈ primChars r, (∫ s, H r χ s)
          ≤ ∑ χ ∈ primChars r, C₀ * N * (T * zp r χ + EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn))) :=
        Finset.sum_le_sum fun χ hχ => (hH r χ hr hχ).2
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
      have hEr := hE0 r
      have hCN : 0 ≤ C₀ * N := mul_nonneg hC₀ hN0
      calc ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, (∫ s, H r χ s)
          ≤ ((r : ℝ) / (Nat.totient r : ℝ)) * (C₀ * N * (T * ∑ χ ∈ primChars r, zp r χ
              + ((primChars r).card : ℝ) * EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn)))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = C₀ * N * (T * (((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, zp r χ)
              + ((r : ℝ) / (Nat.totient r : ℝ) * ((primChars r).card : ℝ))
                * EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn))) := by ring
        _ ≤ _ := by gcongr
    calc _ ≤ ∑ r ∈ Finset.Icc 1 R1, C₀ * N * (T * (((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r, zp r χ)
          + (r : ℝ) * EerrW T (Real.exp s₀) r (K / ((r : ℝ) * Qn))) := Finset.sum_le_sum hper
      _ = C₀ * N * (T * ZS + FE) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hZS, hFE]
  have hL2 : L ≤ 2 * D * (Real.log K + 2) := by rw [hLdef]; nlinarith
  have hP0 : 0 ≤ T ^ 2 * K * (R1 : ℝ) / Qn + T := by positivity
  have hXP : X ≤ (2 * Cp ^ 2 + CU) * (T ^ 2 * K * (R1 : ℝ) / Qn + T) := by
    rw [hXdef]
    have h1 : 0 ≤ T ^ 2 * K * (R1 : ℝ) / Qn := by positivity
    have h2 : 2 * T ^ 2 * Cp ^ 2 * K * (R1 : ℝ) / Qn = 2 * Cp ^ 2 * (T ^ 2 * K * (R1 : ℝ) / Qn) := by ring
    rw [h2]
    have h3 : 0 ≤ 2 * Cp ^ 2 * T := by positivity
    have h4 : 0 ≤ CU * (T ^ 2 * K * (R1 : ℝ) / Qn) := mul_nonneg hCU0 h1
    have e : (2 * Cp ^ 2 + CU) * (T ^ 2 * K * (R1 : ℝ) / Qn + T)
        = (2 * Cp ^ 2 * (T ^ 2 * K * (R1 : ℝ) / Qn) + CU * T) + (2 * Cp ^ 2 * T + CU * (T ^ 2 * K * (R1 : ℝ) / Qn)) := by
      ring
    rw [e]; linarith
  calc (∫ s, W (s - s₀) * RingS Qn T κ Ξ K ε s₀ s) ≤ ∫ s, G s :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hGi (Filter.Eventually.of_forall hbound)
    _ = L * ∑ r ∈ Finset.Icc 1 R1, ((r : ℝ) / (Nat.totient r : ℝ)) *
          ∑ χ ∈ primChars r, (∫ s, H r χ s) + (∫ s, W (s - s₀)) * (L * X) := hGint
    _ ≤ L * (C₀ * N * (T * ZS + FE)) + (2 * N) * (L * X) := by
        gcongr
    _ ≤ 2 * D * (Real.log K + 2) * (C₀ * N * (T * ZS + FE))
          + (2 * N) * (2 * D * (Real.log K + 2) * ((2 * Cp ^ 2 + CU) * (T ^ 2 * K * (R1 : ℝ) / Qn + T))) := by
        have hA1 : 0 ≤ C₀ * N * (T * ZS + FE) := by positivity
        gcongr
    _ ≤ 2 * D * (C₀ + 4 * Cp ^ 2 + 2 * CU) * N * (Real.log K + 2) *
          (T * ZS + FE + (T ^ 2 * K * (R1 : ℝ) / Qn + T)) := by
        have hlk2 : 0 ≤ Real.log K + 2 := by linarith
        have hY : 0 ≤ T * ZS + FE := by positivity
        have e : 2 * D * (C₀ + 4 * Cp ^ 2 + 2 * CU) * N * (Real.log K + 2) *
            (T * ZS + FE + (T ^ 2 * K * (R1 : ℝ) / Qn + T))
            = 2 * D * (Real.log K + 2) * (C₀ * N * (T * ZS + FE))
              + (2 * N) * (2 * D * (Real.log K + 2) * ((2 * Cp ^ 2 + CU) * (T ^ 2 * K * (R1 : ℝ) / Qn + T)))
              + 2 * D * (Real.log K + 2) * N * (C₀ * (T ^ 2 * K * (R1 : ℝ) / Qn + T)
                + (4 * Cp ^ 2 + 2 * CU) * (T * ZS + FE)) := by ring
        rw [e]
        have h3 : 0 ≤ 2 * D * (Real.log K + 2) * N * (C₀ * (T ^ 2 * K * (R1 : ℝ) / Qn + T)
                + (4 * Cp ^ 2 + 2 * CU) * (T * ZS + FE)) := by positivity
        linarith

end ShellS
end ZetaShell

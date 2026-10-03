/-
Node A8 (track K/T, all-marks) — proof of thm:sigd-Sigma and thm:sigd-D (l.1378–1401), abstract: from a FrameFamily for
ψ = cos 1.6s and the two certificates, for every ε > 0 eventually
"(Σ-const − ε)N ≤ Nˢ(I′)" and "(D-const − ε)N ≤ N^d(I′)", with H = 2 − R, (a₁, a₂, ν) of CertAM7.
Deps: A1, A1b, A2, L5 (+ removal (b), node A3), L7, A5, A6 (tight chains), A7 (OL_L), numeric node N2 (robustness
conditions of rem:sigd-robust for k_ψ(3/4)); trunk `eps_form_of_isLittleO`.
Two declarations (the two statistics share every step but Step 3's LP dual).

L2_2, 28 Sep 2026. Statements of `sigma_abstract`, `dist_abstract` unchanged from the skeleton. PROVED modulo the
skeleton nodes L5 (`pair_removal`), L8 (`negIndex_add_le`), A7 (`OLL`), imported from unchanged compiled copies
(deps/*.lean); no `sorry` in this file.
  * Step 2 = `frame_step2`, the per-height "frame inequality" (FI), X cancelled; c* = 2 − 2a₁:
      ‖Ĝ‖² − 2 tr Ĝ ≥ (a₁ − 1)s₁ + a₂s₂ − νΛ + 2(N_H + N_off) − 4(s_H + p) − c*p − o(N),
    o(N) = r_OLL + 2(N(I′) − tr Ĝ). This is lem:sigd-removal(b) (node A3, done here in frame form: Ĝ = G_L + Q,
    Q = G_H + Q_off, n₊(Q) ≤ s_H + p via trunk `posIndex_add_le` and rank G_H ≤ s_H, n₋(Q) ≤ p via L8 and G_H ⪰ 0,
    tr G_L ≤ s₁ + 2s₂ from `gram_eq`), then Σ_{i<p}(λ_i(G_L) − 2)₊² ≤ c*p + ch(G_L), ch(G_L) = ch(M_L) by the
    spectral link `trFun_mul_transpose_comm` (tr f(VVᵀ) = tr f(VᵀV) for f(0) = 0; proved from Mathlib's
    `charpoly_mul_comm'`), G_L = V_LV_Lᵀ, M_L = V_LᵀV_L, V_L = U_L diag(√m); then A7.
  * Step 3 (the LP duals, per-object table) and Step 4 (solve, ε-form): `linarith` from the counts
    n = s₁ + s₂ + s_H, Σm = s₁ + 2s₂ + N_H, N_H ≥ 3s_H, N_off ≥ 4p − 2p₁, p₁ ≤ p, and `eps_form`.
-/
import ZetaS.Interfaces
import Zeta23.LinAlg.Inertia
import ZetaS.LinAlg.L5_PairRemoval
import ZetaS.LinAlg.L8_NegIndexAdd
import ZetaS.Skeleton.A7_OLL

open Filter Asymptotics Finset Matrix RHLinalg

noncomputable section

namespace ZetaS

namespace A8aux

/-! ### counts of a frame -/

lemma pw1 (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) = (if k = 1 then 1 else 0) + (if k = 2 then 1 else 0) + (if 3 ≤ k then 1 else 0) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k <;> simp
  · simp [show k ≠ 1 by omega, show k ≠ 2 by omega, h]

lemma pw2 (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) = (if k = 1 then 1 else 0) + 2 * (if k = 2 then 1 else 0) + (if 3 ≤ k then (k : ℝ) else 0) := by
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k <;> norm_num
  · simp [show k ≠ 1 by omega, show k ≠ 2 by omega, h]

lemma n_eq (F : ZeroFrame) : (F.n : ℝ) = F.sEq 1 + F.sEq 2 + F.sH := by
  unfold ZeroFrame.sEq ZeroFrame.sH
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.natCast_card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => (pw1 (F.m i) (F.one_le_m i)).symm)]
  simp

lemma summ_eq (F : ZeroFrame) : (((∑ i, F.m i : ℕ)) : ℝ) = F.sEq 1 + 2 * F.sEq 2 + F.NH := by
  unfold ZeroFrame.sEq ZeroFrame.NH
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Nat.cast_sum, Nat.cast_sum, Finset.sum_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pw2 (F.m i) (F.one_le_m i)]
  split_ifs <;> first | (exfalso; omega) | simp

lemma NH_ge (F : ZeroFrame) : 3 * (F.sH : ℝ) ≤ F.NH := by
  unfold ZeroFrame.sH ZeroFrame.NH
  have := Finset.card_nsmul_le_sum (univ.filter fun i => 3 ≤ F.m i) F.m 3
    (fun i hi => (Finset.mem_filter.1 hi).2)
  rw [smul_eq_mul] at this
  have h' : ((#(univ.filter fun i => 3 ≤ F.m i) * 3 : ℕ) : ℝ) ≤ ((∑ i ∈ univ.filter fun i => 3 ≤ F.m i, F.m i : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at h' ⊢
  linarith

lemma Noff_ge' (F : ZeroFrame) : 4 * (F.p : ℝ) - 2 * F.p1 ≤ F.Noff := by
  have h1 := F.Noff_ge
  have h2 := F.p1_le
  have : ((2 * F.p1 + 4 * (F.p - F.p1) : ℕ) : ℝ) ≤ (F.Noff : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h2] at this
  push_cast at this
  linarith

lemma Nw_eq (F : ZeroFrame) : (F.Nw : ℝ) = F.sEq 1 + 2 * F.sEq 2 + F.NH + F.Noff := by
  unfold ZeroFrame.Nw
  rw [Nat.cast_add, summ_eq]

/-! ### the ε-form -/

lemma eps_form {N X e : ℝ → ℝ} (hN : ∀ᶠ T in atTop, 0 ≤ N T) {D c0 : ℝ} (hD : 0 < D)
    (he : e =o[atTop] N) (hX : ∀ᶠ T in atTop, c0 * N T - e T ≤ D * X T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c0 / D - ε) * N T ≤ X T := by
  intro ε hε
  have hb := he.bound (mul_pos hε hD)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (hN.and (hb.and hX))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hN0, hbT, hXT⟩ := hT₀ T hT
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at hbT
  have he' : e T ≤ ε * D * N T := (le_abs_self _).trans hbT
  have key : (c0 - ε * D) * N T ≤ D * X T := by nlinarith
  have : (c0 / D - ε) * N T = (c0 - ε * D) * N T / D := by field_simp
  rw [this, div_le_iff₀ hD]
  linarith

end A8aux

/-- **Spectral link**: the nonzero spectra of `VVᵀ` and `VᵀV` agree with multiplicity, so
`tr f(VVᵀ) = tr f(VᵀV)` whenever `f 0 = 0`. -/
theorem trFun_mul_transpose_comm {d k : Type*} [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]
    (V : Matrix d k ℝ) (f : ℝ → ℝ) (hf : f 0 = 0)
    (h1 : (V * Vᵀ).IsHermitian) (h2 : (Vᵀ * V).IsHermitian) : trFun h1 f = trFun h2 f := by
  have hc := Matrix.charpoly_mul_comm' V Vᵀ
  have hr := congrArg Polynomial.roots hc
  have hne1 : (Polynomial.X ^ Fintype.card k * (V * Vᵀ).charpoly : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  have hne2 : (Polynomial.X ^ Fintype.card d * (Vᵀ * V).charpoly : Polynomial ℝ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  rw [Polynomial.roots_mul hne1, Polynomial.roots_mul hne2, Polynomial.roots_X_pow, Polynomial.roots_X_pow,
    h1.roots_charpoly_eq_eigenvalues, h2.roots_charpoly_eq_eigenvalues] at hr
  have hs := congrArg (fun s : Multiset ℝ => (s.map f).sum) hr
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_nsmul, Multiset.sum_nsmul, Multiset.map_singleton,
    Multiset.sum_singleton, hf, smul_zero, zero_add, Multiset.map_map, RCLike.ofReal_real_eq_id,
    Function.id_comp] at hs
  unfold trFun
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  exact hs

namespace A8b

lemma trFun_congr {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) : trFun hA f = trFun hB f := by
  subst h; rfl

lemma rtrace_add {n : Type*} [Fintype n] (A B : Matrix n n ℝ) : rtrace (A + B) = rtrace A + rtrace B := by
  simp [rtrace, Matrix.trace_add]

lemma rtrace_UDUt {d n : ℕ} (U : Matrix (Fin d) (Fin n) ℝ) (w : Fin n → ℝ) :
    rtrace (U * diagonal w * Uᵀ) = ∑ i, w i * (Uᵀ * U) i i := by
  unfold rtrace
  rw [RCLike.re_to_real, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma kappa_bound (cstar t : ℝ) : (max (t - 2) 0) ^ 2 ≤ cstar + kappaCh cstar t := by
  unfold kappaCh
  have := le_max_left ((max (t - 2) 0) ^ 2 - cstar) 0
  linarith

lemma kappa_nonneg (cstar t : ℝ) : 0 ≤ kappaCh cstar t := le_max_right _ _

variable (F : ZeroFrame)

/-- light and heavy weights. -/
def wL (i : Fin F.n) : ℝ := if i ∈ F.light then (F.m i : ℝ) else 0
def wH (i : Fin F.n) : ℝ := if i ∈ F.light then 0 else (F.m i : ℝ)
def GLm : Matrix (Fin F.d) (Fin F.d) ℝ := F.U * diagonal (wL F) * F.Uᵀ
def GHm : Matrix (Fin F.d) (Fin F.d) ℝ := F.U * diagonal (wH F) * F.Uᵀ
def VL : Matrix (Fin F.d) F.light ℝ := Matrix.of fun l j => Real.sqrt (F.m j) * F.U l j

lemma wL_nonneg (i) : 0 ≤ wL F i := by unfold wL; split_ifs <;> positivity
lemma wH_nonneg (i) : 0 ≤ wH F i := by unfold wH; split_ifs <;> positivity

lemma Gt_split : F.Gt = GLm F + (GHm F + F.Qoff) := by
  have : diagonal (fun i => (F.m i : ℝ)) = diagonal (wL F) + diagonal (wH F) := by
    rw [Matrix.diagonal_add]; congr 1; ext i; unfold wL wH; split_ifs <;> simp
  unfold ZeroFrame.Gt GLm GHm
  rw [this, Matrix.mul_add, Matrix.add_mul, add_assoc]

lemma psd_UDUt (w : Fin F.n → ℝ) (hw : ∀ i, 0 ≤ w i) : (F.U * diagonal w * F.Uᵀ).PosSemidef := by
  have h := (Matrix.PosSemidef.diagonal (d := w) (fun i => hw i)).mul_mul_conjTranspose_same F.U
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma GLm_psd : (GLm F).PosSemidef := psd_UDUt F _ (wL_nonneg F)
lemma GHm_psd : (GHm F).PosSemidef := psd_UDUt F _ (wH_nonneg F)

lemma light_iff (i : Fin F.n) : i ∈ F.light ↔ F.m i ≤ 2 := by simp [ZeroFrame.light]

lemma rank_GHm : (GHm F).rank ≤ F.sH := by
  unfold GHm
  calc (F.U * diagonal (wH F) * F.Uᵀ).rank ≤ (F.U * diagonal (wH F)).rank := Matrix.rank_mul_le_left _ _
    _ ≤ (diagonal (wH F)).rank := Matrix.rank_mul_le_right _ _
    _ = Fintype.card {i // wH F i ≠ 0} := Matrix.rank_diagonal _
    _ = #(univ.filter fun i => wH F i ≠ 0) := Fintype.card_subtype _
    _ ≤ F.sH := by
      unfold ZeroFrame.sH
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      unfold wH at hi
      split_ifs at hi with h
      · exact absurd rfl hi
      · rw [light_iff] at h; omega

lemma posIndex_GHm : posIndex (GHm_psd F).isHermitian ≤ F.sH := by
  rw [posIndex_eq_rank_of_posSemidef (GHm_psd F)]; exact rank_GHm F

lemma negIndex_GHm : negIndex (GHm_psd F).isHermitian = 0 := by
  unfold negIndex
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact not_lt.2 ((GHm_psd F).eigenvalues_nonneg i)

lemma diag_le_one (i : Fin F.n) : (F.Uᵀ * F.U) i i ≤ 1 := by
  have h := congrFun (congrFun F.gram_eq i) i
  rw [Matrix.sub_apply] at h
  simp only [kerMat, Matrix.of_apply, sub_self, F.k_zero] at h
  have := F.Etr_psd.diag_nonneg (i := i)
  linarith

lemma sum_wL : ∑ i, wL F i = F.sEq 1 + 2 * F.sEq 2 := by
  unfold ZeroFrame.sEq
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold wL
  have := F.one_le_m i
  by_cases h1 : F.m i = 1
  · simp [light_iff, h1]
  · by_cases h2 : F.m i = 2
    · simp [light_iff, h2]
    · have : ¬ F.m i ≤ 2 := by omega
      simp [light_iff, h1, h2, this]

lemma trace_GLm_le : rtrace (GLm F) ≤ F.sEq 1 + 2 * F.sEq 2 := by
  unfold GLm
  rw [rtrace_UDUt, ← sum_wL]
  apply Finset.sum_le_sum; intro i _
  have := diag_le_one F i
  have := wL_nonneg F i
  nlinarith

lemma GLm_eq_VL : GLm F = VL F * (VL F)ᵀ := by
  ext a b
  have e1 : (F.U * diagonal (wL F) * F.Uᵀ) a b = ∑ j, wL F j * (F.U a j * F.U b j) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]; ring
  have e2 : (VL F * (VL F)ᵀ) a b
      = ∑ j : F.light, Real.sqrt (F.m j) * F.U a j * (Real.sqrt (F.m j) * F.U b j) := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [VL, Matrix.transpose_apply, Matrix.of_apply]
  unfold GLm
  rw [e1, e2, Finset.sum_coe_sort F.light (fun j => Real.sqrt (F.m j) * F.U a j * (Real.sqrt (F.m j) * F.U b j)),
    ← Finset.sum_ite_mem_eq F.light]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold wL
  split_ifs
  · have : Real.sqrt (F.m j) * Real.sqrt (F.m j) = (F.m j : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
    linear_combination (F.U a j * F.U b j) * this.symm
  · simp

lemma ML_eq_VL : F.ML = (VL F)ᵀ * VL F := by
  ext i j
  unfold ZeroFrame.ML VL
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma ML_herm : F.ML.IsHermitian := by
  rw [ML_eq_VL]
  have := Matrix.isHermitian_conjTranspose_mul_self (VL F)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- `Σ_{i<p}(λ_i(G_L) − 2)₊² ≤ c*p + ch(M_L)`. -/
lemma top_sum_le (cstar : ℝ) (hc : 0 ≤ cstar) (hc0 : kappaCh cstar 0 = 0) (p : ℕ) :
    ∑ i : Fin (Fintype.card (Fin F.d)),
        (if (i : ℕ) < p then (max ((GLm_psd F).isHermitian.eigenvalues₀ i - 2) 0) ^ 2 else 0)
      ≤ cstar * p + trFun (ML_herm F) (kappaCh cstar) := by
  set ev0 := (GLm_psd F).isHermitian.eigenvalues₀ with hev
  have h1 : ∀ i : Fin (Fintype.card (Fin F.d)),
      (if (i : ℕ) < p then (max (ev0 i - 2) 0) ^ 2 else 0)
        ≤ (if (i : ℕ) < p then cstar else 0) + kappaCh cstar (ev0 i) := by
    intro i
    split_ifs
    · exact kappa_bound _ _
    · simpa using kappa_nonneg cstar (ev0 i)
  have h2 : ∑ i : Fin (Fintype.card (Fin F.d)), (if (i : ℕ) < p then cstar else 0) ≤ cstar * p := by
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < p then cstar else 0), ← Finset.sum_filter]
    calc ∑ j ∈ (range (Fintype.card (Fin F.d))).filter (fun j => j < p), cstar
        ≤ ∑ j ∈ range p, cstar := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj; simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢; exact hj.2
          · intro _ _ _; exact hc
      _ = cstar * p := by rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_comm]
  have h3 : ∑ i, kappaCh cstar (ev0 i) = trFun (ML_herm F) (kappaCh cstar) := by
    rw [hev, ← sum_eigenvalues_reindex (GLm_psd F).isHermitian (kappaCh cstar)]
    change trFun (GLm_psd F).isHermitian (kappaCh cstar) = _
    have hA : (VL F * (VL F)ᵀ).IsHermitian := GLm_eq_VL F ▸ (GLm_psd F).isHermitian
    have hB : ((VL F)ᵀ * VL F).IsHermitian := ML_eq_VL F ▸ ML_herm F
    rw [trFun_congr (GLm_eq_VL F) _ hA, trFun_mul_transpose_comm (VL F) _ hc0 hA hB,
      trFun_congr (ML_eq_VL F).symm hB (ML_herm F)]
  calc _ ≤ ∑ i : Fin (Fintype.card (Fin F.d)), ((if (i : ℕ) < p then cstar else 0) + kappaCh cstar (ev0 i)) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = _ := by rw [Finset.sum_add_distrib]
    _ ≤ cstar * p + trFun (ML_herm F) (kappaCh cstar) := by rw [h3]; linarith

/-- (FI) at one height, given the OLL bound at that height. -/
lemma frame_ineq_at (cstar a1 a2 ν ρ : ℝ) (hc : 0 ≤ cstar) (hc0 : kappaCh cstar 0 = 0)
    (hOLL : trFun (ML_herm F) (kappaCh cstar)
      ≤ F.slackOn F.light (F.sEq 1) - a1 * (F.sEq 1 : ℝ) - a2 * (F.sEq 2 : ℝ) + ν * F.Λ + ρ) :
    (a1 - 1) * (F.sEq 1 : ℝ) + a2 * (F.sEq 2 : ℝ) - ν * F.Λ + 2 * ((F.NH : ℝ) + F.Noff)
        - 4 * ((F.sH : ℝ) + F.p) - cstar * (F.p : ℝ) - (ρ + 2 * ((F.Nw : ℝ) - rtrace F.Gt))
      ≤ frobSq F.Gt - 2 * rtrace F.Gt := by
  have hQ : (GHm F + F.Qoff).IsHermitian := (GHm_psd F).isHermitian.add F.Qoff_herm
  have hb : posIndex hQ ≤ F.sH + F.p :=
    (posIndex_add_le (GHm_psd F).isHermitian F.Qoff_herm).trans (add_le_add (posIndex_GHm F) F.nplus_off)
  have hp : negIndex hQ ≤ F.p := by
    have := negIndex_add_le (GHm_psd F).isHermitian F.Qoff_herm
    rw [negIndex_GHm, zero_add] at this
    exact this.trans F.nminus_off
  have hL5 := pair_removal (GLm_psd F) hQ hb hp
  have hSig := top_sum_le F cstar hc hc0 F.p
  have hsplit := Gt_split F
  have htr : rtrace F.Gt = rtrace (GLm F) + rtrace (GHm F + F.Qoff) := by rw [hsplit, rtrace_add]
  have hfr : frobSq F.Gt = frobSq (GLm F + (GHm F + F.Qoff)) := by rw [hsplit]
  have hslack : F.slackOn F.light (F.sEq 1) = (F.sEq 1 : ℝ) - 2 * rtrace (GLm F) + frobSq (GLm F) := rfl
  have hGLtr := trace_GLm_le F
  have hNw := A8aux.Nw_eq F
  have hbR : ((F.sH + F.p : ℕ) : ℝ) = (F.sH : ℝ) + F.p := by push_cast; ring
  rw [hbR] at hL5
  linarith

end A8b

open A8b

/-- **(FI)**, Step 2 of the proof of thm:sigd-Sigma/D with X cancelled; proved from L5, L8, A7 and the spectral link. -/
theorem frame_step2 {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) (hmaj : CertMaj) :
    ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop,
      (1824837 / 10 ^ 8 - 1) * ((Fm.F T).sEq 1 : ℝ) + 1168069 / (5 * 10 ^ 7) * ((Fm.F T).sEq 2 : ℝ)
          - 3 / 250 * (Fm.F T).Λ + 2 * (((Fm.F T).NH : ℝ) + (Fm.F T).Noff)
          - 4 * (((Fm.F T).sH : ℝ) + (Fm.F T).p) - (2 - 2 * (1824837 / 10 ^ 8)) * ((Fm.F T).p : ℝ) - r T
        ≤ RHLinalg.frobSq (Fm.F T).Gt - 2 * RHLinalg.rtrace (Fm.F T).Gt := by
  obtain ⟨ρ, hρ, hOLL⟩ := OLL Fm hcert hmaj (fun T => ML_herm (Fm.F T))
  refine ⟨fun T => ρ T + 2 * (((Fm.F T).Nw : ℝ) - rtrace (Fm.F T).Gt), ?_, ?_⟩
  · have := (hρ.add (Fm.window.const_mul_left 2)).sub (Fm.trace.const_mul_left 2)
    exact this.congr_left (fun T => by ring)
  · filter_upwards [hOLL] with T hT
    have hc : (0 : ℝ) ≤ 2 - 2 * (1824837 / 10 ^ 8) := by norm_num
    have hc0 : kappaCh (2 - 2 * (1824837 / 10 ^ 8)) 0 = 0 := by
      unfold kappaCh; norm_num
    exact frame_ineq_at (Fm.F T) _ _ _ _ _ hc hc0 hT


open A8aux

theorem sigma_abstract {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) (hmaj : CertMaj) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (sigmaConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NsW : ℝ) := by
  obtain ⟨r, hr, hFI⟩ := frame_step2 Fm hcert hmaj
  obtain ⟨r', hr', hspan⟩ := Fm.span
  let e : ℝ → ℝ := fun T => -((1168069 / (5 * 10 ^ 7) : ℝ) / 2 * (((Fm.F T).Nw : ℝ) - N T)
      + 2 * (RHLinalg.rtrace (Fm.F T).Gt - N T)
      - (RHLinalg.frobSq (Fm.F T).Gt - R * N T) - r T - (3 / 250 : ℝ) * r' T)
  have he : e =o[atTop] N := by
    have := (((((Fm.window.const_mul_left ((1168069 / (5 * 10 ^ 7) : ℝ) / 2)).add
      (Fm.trace.const_mul_left 2)).sub Fm.frob).sub hr).sub (hr'.const_mul_left (3 / 250 : ℝ))).neg_left
    exact this.congr_left (fun T => rfl)
  have hD : (0 : ℝ) < 1 - 1824837 / 10 ^ 8 + 1168069 / (5 * 10 ^ 7) / 2 := by norm_num
  have hmain := eps_form (X := fun T => ((Fm.F T).NsW : ℝ))
    (c0 := (2 - R) + 1168069 / (5 * 10 ^ 7) / 2 - 3 / 250) Fm.N_nonneg hD he (by
    filter_upwards [hFI, hspan] with T hT hsp
    have c3 := NH_ge (Fm.F T); have c4 := Noff_ge' (Fm.F T); have c5 := Nw_eq (Fm.F T)
    have hp1 : ((Fm.F T).p1 : ℝ) ≤ (Fm.F T).p := by exact_mod_cast (Fm.F T).p1_le
    have hX : ((Fm.F T).NsW : ℝ) = (Fm.F T).sEq 1 + 2 * (Fm.F T).p1 := by
      unfold ZeroFrame.NsW; push_cast; ring
    have hsH : (0 : ℝ) ≤ (Fm.F T).sH := Nat.cast_nonneg _
    simp only [e]
    rw [hX]
    linarith)
  intro ε hε
  obtain ⟨T₀, h⟩ := hmain ε hε
  exact ⟨T₀, fun T hT => by unfold sigmaConst; exact h T hT⟩

theorem dist_abstract {N : ℝ → ℝ} {R : ℝ} (Fm : FrameFamily N R (kPsi psiCos16))
    (hcert : CertAM7) (hmaj : CertMaj) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (distConst (2 - R) (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (3 / 250) - ε) * N T
        ≤ ((Fm.F T).NdW : ℝ) := by
  obtain ⟨r, hr, hFI⟩ := frame_step2 Fm hcert hmaj
  obtain ⟨r', hr', hspan⟩ := Fm.span
  let e : ℝ → ℝ := fun T => -((1 + 1168069 / (5 * 10 ^ 7) - 1824837 / 10 ^ 8 : ℝ) * (((Fm.F T).Nw : ℝ) - N T)
      + 2 * (RHLinalg.rtrace (Fm.F T).Gt - N T)
      - (RHLinalg.frobSq (Fm.F T).Gt - R * N T) - r T - (3 / 250 : ℝ) * r' T)
  have he : e =o[atTop] N := by
    have := (((((Fm.window.const_mul_left (1 + 1168069 / (5 * 10 ^ 7) - 1824837 / 10 ^ 8 : ℝ)).add
      (Fm.trace.const_mul_left 2)).sub Fm.frob).sub hr).sub (hr'.const_mul_left (3 / 250 : ℝ))).neg_left
    exact this.congr_left (fun T => rfl)
  have hD : (0 : ℝ) < 2 - 2 * (1824837 / 10 ^ 8) + 1168069 / (5 * 10 ^ 7) := by norm_num
  have hmain := eps_form (X := fun T => ((Fm.F T).NdW : ℝ))
    (c0 := 1 + (2 - R) + 1168069 / (5 * 10 ^ 7) - 1824837 / 10 ^ 8 - 3 / 250) Fm.N_nonneg hD he (by
    filter_upwards [hFI, hspan] with T hT hsp
    have c1 := n_eq (Fm.F T); have c3 := NH_ge (Fm.F T); have c4 := Noff_ge' (Fm.F T)
    have c5 := Nw_eq (Fm.F T)
    have hp1 : ((Fm.F T).p1 : ℝ) ≤ (Fm.F T).p := by exact_mod_cast (Fm.F T).p1_le
    have hX : ((Fm.F T).NdW : ℝ) = (Fm.F T).n + 2 * (Fm.F T).p := by
      unfold ZeroFrame.NdW; push_cast; ring
    have hsH : (0 : ℝ) ≤ (Fm.F T).sH := Nat.cast_nonneg _
    simp only [e]
    rw [hX]
    linarith)
  intro ε hε
  obtain ⟨T₀, h⟩ := hmain ε hε
  exact ⟨T₀, fun T hT => by unfold distConst; exact h T hT⟩

end ZetaS

end

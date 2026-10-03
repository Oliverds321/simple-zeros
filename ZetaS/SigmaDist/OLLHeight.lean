/-
OLLHeight (L4_1, 28 Sep 2026) — node A7 (thm:sigd-OLL, sec_zeta.tex l.1320–1345) at ONE height, as a deterministic
inequality for a `ZeroFrame` F whose kernel is ε-close to k_ψ (ψ = cos 1.6s) and (1 + e′)k_ψ-dominated:
  ch(M_L) ≤ Slack(𝒪_L) − a₁s₁ − a₂s₂ + νΛ + 788·Σ m_ρδ_ρ + 784·ε·n + 14·B,      B = Σ_i(|b_i(1)| + |b_i(2)|),
provided ε ≤ 1/20 and e′ ≤ 1/40 (the draft's "T ≥ T₀").
Route (the draft's): 𝒯 = light sites with another light site closer than 3/4, ℛ = the other light sites;
  (1) A5 (`separated_room`) + Ê ⪰ 0 ⇒ λ_max(M_ℛ) ≤ (1 + e′)β ≤ 2 + √c* for any majorant threshold β ≤ 33/10
      (CertMaj: β = 3.2063638853, or 33/10 after the lead's restatement) and e′ ≤ 1/40;
  (2) L7 (`schur_localisation`) after reindexing M_L ≅ [[M_𝒯, M_𝒯ℛ],[M_ℛ𝒯, M_ℛ]];
  (3) A6 (`tight_chains`, new node) with k* = 1/4 − ε (N2: k_ψ(3/4) ≥ 1/4; N3: k_ψ antitone on [0,1]);
  (4) A2 (corrected form `agg_true_window_of_symm`) on ℛ; (5) A1 on 𝒪_L, A1b on ℛ; (6) the accounting.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L7_SchurLocalisation
import ZetaS.SigmaDist.A1_OnSlackIdentity
import ZetaS.SigmaDist.A1b_BetaBound
import ZetaS.SigmaDist.A2_AggTrueWindow
import ZetaS.SigmaDist.A5_SeparatedRoom
import ZetaS.Skeleton.A6_TightChains
import ZetaS.SigmaDist.N2_KPsiThreeQuarters
import ZetaS.SigmaDist.N3_KernelAntitone
import ZetaS.SigmaDist.SigmaHelpers
import ZetaS.SigmaDist.OLLHelpers

noncomputable section

open Matrix RHLinalg Finset

namespace ZetaS
namespace OLL

attribute [local instance low] Classical.propDecidable

variable (F : ZeroFrame)

/-! ### the true Gram matrix and its entries -/

def Cg : Matrix (Fin F.n) (Fin F.n) ℝ := F.Uᵀ * F.U

def Mf : Matrix (Fin F.n) (Fin F.n) ℝ :=
  Matrix.of fun i j => Real.sqrt ((F.m i : ℝ) * F.m j) * Cg F i j

lemma Cg_eq : Cg F = kerMat F.k F.x - F.Etr := F.gram_eq

lemma Cg_apply (i j : Fin F.n) : Cg F i j = F.k (F.x i - F.x j) - F.Etr i j := by
  rw [Cg_eq]; simp [kerMat]

lemma Cg_psd : (Cg F).PosSemidef := by
  have := Matrix.posSemidef_conjTranspose_mul_self F.U
  simpa [Cg, Matrix.conjTranspose_eq_transpose_of_trivial] using this

lemma Cg_symm (i j : Fin F.n) : Cg F i j = Cg F j i := by
  simp only [Cg, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma delta_nonneg (i : Fin F.n) : 0 ≤ F.delta i := F.Etr_psd.diag_nonneg

lemma Cg_diag (i : Fin F.n) : Cg F i i = 1 - F.delta i := by
  rw [Cg_apply]; simp [F.k_zero, ZeroFrame.delta]

lemma delta_le_one (i : Fin F.n) : F.delta i ≤ 1 := by
  have := (Cg_psd F).diag_nonneg (i := i); rw [Cg_diag] at this; linarith

lemma Cg_abs_le_one (i j : Fin F.n) : |Cg F i j| ≤ 1 := by
  have h := psd_entry_sq_le (Cg_psd F) i j
  rw [Cg_diag, Cg_diag] at h
  have := delta_nonneg F i; have := delta_nonneg F j; have := delta_le_one F i; have := delta_le_one F j
  exact (sq_le_one_iff_abs_le_one _).mp (by nlinarith)

lemma Etr_abs_le (i j : Fin F.n) : |F.Etr i j| ≤ Real.sqrt (F.delta i * F.delta j) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (psd_entry_sq_le F.Etr_psd i j)

lemma Cg_close {kψ : ℝ → ℝ} {e : ℝ} (he : ∀ t, |F.k t - kψ t| ≤ e) (i j : Fin F.n) :
    |Cg F i j - kψ (F.x i - F.x j)| ≤ e + Real.sqrt (F.delta i * F.delta j) := by
  rw [Cg_apply]
  have h1 := he (F.x i - F.x j); have h2 := Etr_abs_le F i j
  have h3 := abs_add_le (F.k (F.x i - F.x j) - kψ (F.x i - F.x j)) (-F.Etr i j)
  rw [abs_neg] at h3
  have h4 : F.k (F.x i - F.x j) - F.Etr i j - kψ (F.x i - F.x j)
      = (F.k (F.x i - F.x j) - kψ (F.x i - F.x j)) + -F.Etr i j := by ring
  rw [h4]; linarith

lemma k_abs_le_one (t : ℝ) : |F.k t| ≤ 1 := by
  have h := psd_entry_sq_le (F.k_posDef 2 ![0, t]) 0 1
  simp only [kerMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, zero_sub,
    F.k_zero, F.k_even, mul_one] at h
  exact (sq_le_one_iff_abs_le_one _).mp h

lemma Mf_symm (i j : Fin F.n) : Mf F i j = Mf F j i := by
  simp only [Mf, Matrix.of_apply, Cg_symm F i j, mul_comm (F.m i : ℝ)]

lemma Mf_sq (i j : Fin F.n) : Mf F i j ^ 2 = (F.m i : ℝ) * F.m j * Cg F i j ^ 2 := by
  simp only [Mf, Matrix.of_apply, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (F.m i : ℝ) * F.m j)]

lemma Mf_diag (i : Fin F.n) : Mf F i i = (F.m i : ℝ) * Cg F i i := by
  simp only [Mf, Matrix.of_apply, Real.sqrt_mul_self (Nat.cast_nonneg (F.m i))]

lemma light_iff (i : Fin F.n) : i ∈ F.light ↔ F.m i ≤ 2 := by simp [ZeroFrame.light]

lemma light_m (i : Fin F.n) (hi : i ∈ F.light) : F.m i = 1 ∨ F.m i = 2 := by
  have := (light_iff F i).1 hi; have := F.one_le_m i; omega

/-! ### the split 𝒯 ∪ ℛ of the light sites -/

def close (i : Fin F.n) : Prop := ∃ j ∈ F.light, j ≠ i ∧ |F.x i - F.x j| < 3 / 4

def Tset : Finset (Fin F.n) := F.light.filter (close F)

def Rset : Finset (Fin F.n) := F.light.filter (fun i => ¬ close F i)

def eT : Fin (Tset F).card ↪o Fin F.n := (Tset F).orderEmbOfFin rfl
def eR : Fin (Rset F).card ↪o Fin F.n := (Rset F).orderEmbOfFin rfl

lemma eT_mem (i : Fin (Tset F).card) : eT F i ∈ Tset F := (Tset F).orderEmbOfFin_mem rfl i
lemma eR_mem (i : Fin (Rset F).card) : eR F i ∈ Rset F := (Rset F).orderEmbOfFin_mem rfl i

lemma T_sub : Tset F ⊆ F.light := by unfold Tset; exact filter_subset _ _
lemma R_sub : Rset F ⊆ F.light := by unfold Rset; exact filter_subset _ _

lemma TR_disj : Disjoint (Tset F) (Rset F) := by
  unfold Tset Rset; exact disjoint_filter_filter_not _ _ _

lemma TR_union : Tset F ∪ Rset F = F.light := by
  unfold Tset Rset; exact filter_union_filter_not_eq _ _

lemma mem_T_close {i : Fin F.n} (hi : i ∈ Tset F) : close F i := by
  unfold Tset at hi; exact (mem_filter.1 hi).2

lemma mem_R_notclose {i : Fin F.n} (hi : i ∈ Rset F) : ¬ close F i := by
  unfold Rset at hi; exact (mem_filter.1 hi).2

lemma sum_light (g : Fin F.n → ℝ) : ∑ i ∈ F.light, g i = ∑ i ∈ Tset F, g i + ∑ i ∈ Rset F, g i := by
  rw [← TR_union F, sum_union (TR_disj F)]

lemma mem_range_eT {i : Fin F.n} (hi : i ∈ Tset F) : ∃ a, eT F a = i := by
  have : i ∈ Set.range (eT F) := by rw [eT, Finset.range_orderEmbOfFin]; exact hi
  exact this

lemma mem_range_eR {i : Fin F.n} (hi : i ∈ Rset F) : ∃ a, eR F a = i := by
  have : i ∈ Set.range (eR F) := by rw [eR, Finset.range_orderEmbOfFin]; exact hi
  exact this

/-! ### the reindexing `M_L ≅ [[M_𝒯, M_𝒯ℛ], [M_ℛ𝒯, M_ℛ]]` -/

def sig : Fin (Tset F).card ⊕ Fin (Rset F).card → F.light :=
  Sum.elim (fun i => ⟨eT F i, T_sub F (eT_mem F i)⟩) (fun j => ⟨eR F j, R_sub F (eR_mem F j)⟩)

lemma sig_bij : Function.Bijective (sig F) := by
  constructor
  · rintro (i | i) (j | j) h <;> simp only [sig, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at h
    · exact congrArg Sum.inl ((eT F).injective h)
    · exact absurd (TR_disj F) (Finset.not_disjoint_iff.mpr ⟨_, eT_mem F i, by rw [h]; exact eR_mem F j⟩)
    · exact absurd (TR_disj F) (Finset.not_disjoint_iff.mpr ⟨_, eT_mem F j, by rw [← h]; exact eR_mem F i⟩)
    · exact congrArg Sum.inr ((eR F).injective h)
  · rintro ⟨i, hi⟩
    rw [← TR_union F, Finset.mem_union] at hi
    rcases hi with hi | hi
    · obtain ⟨a, ha⟩ := mem_range_eT F hi
      exact ⟨Sum.inl a, by simp [sig, ha]⟩
    · obtain ⟨a, ha⟩ := mem_range_eR F hi
      exact ⟨Sum.inr a, by simp [sig, ha]⟩

def sigE : (Fin (Tset F).card ⊕ Fin (Rset F).card) ≃ F.light := Equiv.ofBijective (sig F) (sig_bij F)

def MT : Matrix (Fin (Tset F).card) (Fin (Tset F).card) ℝ := (Mf F).submatrix (eT F) (eT F)
def MY : Matrix (Fin (Tset F).card) (Fin (Rset F).card) ℝ := (Mf F).submatrix (eT F) (eR F)
def MR : Matrix (Fin (Rset F).card) (Fin (Rset F).card) ℝ := (Mf F).submatrix (eR F) (eR F)

lemma MT_herm : (MT F).IsHermitian := by
  ext i j; simp [MT, Matrix.conjTranspose_apply, Mf_symm F (eT F i)]

lemma MR_herm : (MR F).IsHermitian := by
  ext i j; simp [MR, Matrix.conjTranspose_apply, Mf_symm F (eR F i)]

lemma blocks_eq : fromBlocks (MT F) (MY F) (MY F)ᴴ (MR F) = reindex (sigE F).symm (sigE F).symm F.ML := by
  ext s t
  rcases s with i | i <;> rcases t with j | j
  · rfl
  · rfl
  · simp only [fromBlocks_apply₂₁, conjTranspose_apply, star_trivial, MY, submatrix_apply]
    rw [Mf_symm]; rfl
  · rfl

lemma schur_step (hML : F.ML.IsHermitian) {cstar : ℝ} (hc : 0 ≤ cstar)
    (hRmax : ∀ i, (MR_herm F).eigenvalues i ≤ 2 + Real.sqrt cstar) :
    trFun hML (kappaCh cstar) ≤ frobSq (MT F - 2) + 2 * (∑ i, ∑ j, (MY F i j) ^ 2)
      - trFun (MT_herm F) (fun t => (max (2 - t) 0) ^ 2) := by
  have hL7 := schur_localisation (MY F) (MT_herm F) (MR_herm F) hc hRmax
  have hFB0 := (MT_herm F).fromBlocks (B := MY F) (C := (MY F)ᴴ) rfl (MR_herm F)
  have hFB : (reindex (sigE F).symm (sigE F).symm F.ML).IsHermitian := by rw [← blocks_eq]; exact hFB0
  rw [← trFun_reindex (sigE F).symm hML hFB, ← trFun_congr (blocks_eq F) hFB0 hFB]
  exact hL7

/-! ### (1) λ_max(M_ℛ) from A5 -/

lemma form_eq {k : Type*} [Fintype k] (A : Matrix k k ℝ) (y : k → ℝ) :
    y ⬝ᵥ (A *ᵥ y) = ∑ a, ∑ b, y a * y b * A a b := by
  simp only [dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma R_sep {i j : Fin F.n} (hi : i ∈ Rset F) (hj : j ∈ Rset F) (hij : j ≠ i) : 3 / 4 ≤ |F.x i - F.x j| := by
  by_contra h
  exact mem_R_notclose F hi ⟨j, R_sub F hj, hij, lt_of_not_ge h⟩

lemma MR_form {β e : ℝ} (hmaj : MajorantCert psiCos16 β) (he : 0 ≤ e)
    (hdom : IsPosDefKernel (fun t => (1 + e) * kPsi psiCos16 t - F.k t)) (y : Fin (Rset F).card → ℝ) :
    y ⬝ᵥ (MR F *ᵥ y) ≤ (1 + e) * β * ∑ a, y a ^ 2 := by
  have hsep : ∀ i j : Fin (Rset F).card, i < j → F.x (eR F i) + 3 / 4 ≤ F.x (eR F j) := by
    intro i j hij
    have hlt : eR F i < eR F j := (eR F).strictMono hij
    have hx : F.x (eR F i) < F.x (eR F j) := F.x_mono hlt
    have h := R_sep F (eR_mem F i) (eR_mem F j) (ne_of_gt hlt)
    rw [abs_of_neg (by linarith)] at h
    linarith
  have hm : ∀ i, F.m (eR F i) = 1 ∨ F.m (eR F i) = 2 := fun i => light_m F _ (R_sub F (eR_mem F i))
  have hA5 := separated_room hmaj he hdom (fun i => F.x (eR F i)) hsep (fun i => F.m (eR F i)) hm y
  set z : Fin (Rset F).card → ℝ := fun a => y a * Real.sqrt (F.m (eR F a)) with hz
  have hE := (F.Etr_psd.submatrix (eR F)).dotProduct_mulVec_nonneg z
  simp only [star_trivial] at hE
  rw [form_eq] at hE ⊢
  have key : ∀ a b, y a * y b * MR F a b
      = y a * y b * Real.sqrt ((F.m (eR F a) : ℝ) * F.m (eR F b)) * F.k (F.x (eR F a) - F.x (eR F b))
        - z a * z b * F.Etr.submatrix (eR F) (eR F) a b := by
    intro a b
    simp only [MR, Mf, submatrix_apply, Matrix.of_apply, Cg_apply, hz,
      Real.sqrt_mul (Nat.cast_nonneg (F.m (eR F a)))]
    ring
  simp only [key, Finset.sum_sub_distrib] at ⊢
  linarith

lemma cstar_bounds : (0 : ℝ) ≤ 2 - 2 * (1824837 / 10 ^ 8) ∧ (7 / 5 : ℝ) ≤ Real.sqrt (2 - 2 * (1824837 / 10 ^ 8)) := by
  refine ⟨by norm_num, ?_⟩
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

lemma MR_eig {β e : ℝ} (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10) (he : 0 ≤ e) (he1 : e ≤ 1 / 40)
    (hdom : IsPosDefKernel (fun t => (1 + e) * kPsi psiCos16 t - F.k t)) (i : Fin (Rset F).card) :
    (MR_herm F).eigenvalues i ≤ 2 + Real.sqrt (2 - 2 * (1824837 / 10 ^ 8)) := by
  have h := eig_le_of_form (MR_herm F) (MR_form F hmaj he hdom) i
  have hs := cstar_bounds.2
  have : (1 + e) * β ≤ 2 + 7 / 5 := by rcases le_total 0 β with hb | hb <;> nlinarith
  linarith


/-! ### (3) the tight sites: A6 with k* = 1/4 − ε -/

lemma T_tight (i : Fin (Tset F).card) : ∃ j, j ≠ i ∧ |F.x (eT F i) - F.x (eT F j)| < 3 / 4 := by
  obtain ⟨j, hjL, hji, hlt⟩ := mem_T_close F (eT_mem F i)
  have hjT : j ∈ Tset F := by
    unfold Tset; rw [mem_filter]
    exact ⟨hjL, eT F i, T_sub F (eT_mem F i), fun h => hji h.symm, by rw [abs_sub_comm]; exact hlt⟩
  obtain ⟨b, hb⟩ := mem_range_eT F hjT
  exact ⟨b, fun h => hji (by rw [← hb, h]), by rw [hb]; exact hlt⟩

lemma MT_eq : MT F = Matrix.of fun i j => Real.sqrt ((F.m (eT F i) : ℝ) * F.m (eT F j))
    * (kerMat F.k (fun i => F.x (eT F i)) - F.Etr.submatrix (eT F) (eT F)) i j := by
  ext i j; simp [MT, Mf, Cg_apply, kerMat]

lemma psi_cont : ContinuousOn psiCos16 (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
  (by unfold psiCos16; fun_prop : Continuous psiCos16).continuousOn

lemma psi_pos : ∀ s ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), 0 < psiCos16 s := by
  intro s hs
  unfold psiCos16
  apply Real.cos_pos_of_mem_Ioo
  have := Real.pi_gt_three
  have h1 := hs.1; have h2 := hs.2
  constructor <;> nlinarith

lemma kpsi_abs (t : ℝ) : |kPsi psiCos16 t| ≤ 1 := SigmaHelpers.kPsi_abs_le_one psi_cont psi_pos t

lemma kpsi_close (t : ℝ) (ht : |t| < 3 / 4) : 1 / 4 ≤ kPsi psiCos16 t := by
  have hanti := kPsi_antitoneOn psi_cont psi_pos
  have h34 := kPsi_cos16_three_quarters
  have heven : kPsi psiCos16 t = kPsi psiCos16 |t| := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, SigmaHelpers.kPsi_neg]
  rw [heven]
  have : kPsi psiCos16 (3 / 4) ≤ kPsi psiCos16 |t| :=
    hanti ⟨abs_nonneg t, by linarith⟩ ⟨by norm_num, by norm_num⟩ ht.le
  linarith

lemma T_adj (i : Fin (Tset F).card) : ∃ j : Fin (Tset F).card, (j.val + 1 = i.val ∨ i.val + 1 = j.val) ∧
    |F.x (eT F i) - F.x (eT F j)| < 3 / 4 := by
  obtain ⟨j, hji, hlt⟩ := T_tight F i
  have hy : StrictMono (fun a => F.x (eT F a)) := F.x_mono.comp (eT F).strictMono
  rcases lt_or_gt_of_ne hji with h | h
  · have hv : j.val < i.val := h
    refine ⟨⟨i.val - 1, by omega⟩, Or.inl (by simp only; omega), ?_⟩
    have h1 : j ≤ ⟨i.val - 1, by omega⟩ := by rw [Fin.le_def]; simp only; omega
    have h2 : (⟨i.val - 1, by omega⟩ : Fin (Tset F).card) < i := by rw [Fin.lt_def]; simp only; omega
    have e1 := hy.monotone h1; have e2 := hy h2; have e3 := hy h
    simp only at e1 e2 e3
    rw [abs_of_pos (by linarith)]; rw [abs_of_pos (by linarith)] at hlt; linarith
  · have hv : i.val < j.val := h
    refine ⟨⟨i.val + 1, by omega⟩, Or.inr (by simp only), ?_⟩
    have h1 : (⟨i.val + 1, by omega⟩ : Fin (Tset F).card) ≤ j := by rw [Fin.le_def]; simp only; omega
    have h2 : i < (⟨i.val + 1, by omega⟩ : Fin (Tset F).card) := by rw [Fin.lt_def]; simp only; omega
    have e1 := hy.monotone h1; have e2 := hy h2; have e3 := hy h
    simp only at e1 e2 e3
    rw [abs_of_neg (by linarith)]; rw [abs_of_neg (by linarith)] at hlt; linarith

lemma mu_ge {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 20) :
    max (1824837 / 10 ^ 8 : ℝ) (1168069 / (5 * 10 ^ 7))
      ≤ muTight (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (1 / 4 - e) := by
  have hk5 : (1 / 5 : ℝ) ≤ 1 / 4 - e := by linarith
  have hk2 : (1 / 25 : ℝ) ≤ (1 / 4 - e) ^ 2 := by nlinarith
  have hs : (57 / 100 : ℝ) ≤ Real.sqrt (1 / 4 + 2 * (1 / 4 - e) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  rw [max_eq_right (by norm_num)]
  unfold muTight
  refine le_min (le_min (by nlinarith) (by nlinarith)) ?_
  nlinarith

lemma sum_eT (g : Fin F.n → ℝ) : ∑ i, g (eT F i) = ∑ i ∈ Tset F, g i := sum_orderEmb _ _

lemma tight_part {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 20) (hke : ∀ t, |F.k t - kPsi psiCos16 t| ≤ e) :
    (1 + 1824837 / 10 ^ 8) * (∑ i ∈ Tset F, if F.m i = 1 then (1 : ℝ) else 0)
      + 1168069 / (5 * 10 ^ 7) * (∑ i ∈ Tset F, if F.m i = 2 then (1 : ℝ) else 0)
      ≤ trFun (MT_herm F) (fun t => (max (2 - t) 0) ^ 2) := by
  have hC : (kerMat F.k (fun i => F.x (eT F i)) - F.Etr.submatrix (eT F) (eT F)).PosSemidef := by
    have h := (Cg_psd F).submatrix (eT F)
    convert h using 1
    ext i j; simp [Cg_apply, kerMat]
  have hM : (Matrix.of fun i j => Real.sqrt ((F.m (eT F i) : ℝ) * F.m (eT F j))
      * (kerMat F.k (fun i => F.x (eT F i)) - F.Etr.submatrix (eT F) (eT F)) i j).IsHermitian := by
    rw [← MT_eq]; exact MT_herm F
  have hmu := mu_ge he0 he1
  have hmax0 : (0 : ℝ) ≤ max (1824837 / 10 ^ 8 : ℝ) (1168069 / (5 * 10 ^ 7)) := by norm_num
  have hA6 := tight_chains (fun i => F.x (eT F i)) (F.x_mono.comp (eT F).strictMono) (T_adj F)
    (fun i => F.m (eT F i)) (fun i => light_m F _ (T_sub F (eT_mem F i))) F.k F.k_zero (k_abs_le_one F) F.k_even
    (kstar := 1 / 4 - e) (by linarith)
    (a₁ := 1824837 / 10 ^ 8) (a₂ := 1168069 / (5 * 10 ^ 7))
    (fun t ht0 ht => by
      have h1 := (abs_le.1 (hke t)).1
      have h2 := kpsi_close t (by rw [abs_of_nonneg ht0]; exact ht)
      linarith)
    (F.Etr.submatrix (eT F) (eT F)) (F.Etr_psd.submatrix _) hC (by norm_num) (by norm_num)
    (by linarith) hM
  have hnc : (0 : ℝ) ≤ (nChains (fun i => F.x (eT F i)) : ℝ)
      * (muTight (1824837 / 10 ^ 8) (1168069 / (5 * 10 ^ 7)) (1 / 4 - e)
          - max (1824837 / 10 ^ 8 : ℝ) (1168069 / (5 * 10 ^ 7))) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hsum : (∑ i, (if F.m (eT F i) = 1 then 1 + 1824837 / 10 ^ 8 else (1168069 / (5 * 10 ^ 7) : ℝ)))
      = (1 + 1824837 / 10 ^ 8) * (∑ i ∈ Tset F, if F.m i = 1 then (1 : ℝ) else 0)
        + 1168069 / (5 * 10 ^ 7) * (∑ i ∈ Tset F, if F.m i = 2 then (1 : ℝ) else 0) := by
    rw [sum_eT F (fun i => if F.m i = 1 then 1 + 1824837 / 10 ^ 8 else (1168069 / (5 * 10 ^ 7) : ℝ)),
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i hi
    rcases light_m F i (T_sub F hi) with h | h <;> simp [h]
  rw [trFun_congr (MT_eq F) (MT_herm F) hM, ← hsum]
  linarith

/-! ### (4) A2 on ℛ -/

lemma agg_R {W : MarkWeights 7} (hcert : LocalCertAM (kPsi psiCos16) W) {e : ℝ} (he0 : 0 ≤ e)
    (hke : ∀ t, |F.k t - kPsi psiCos16 t| ≤ e) :
    W.a 0 * (#(univ.filter fun i => F.m (eR F i) = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ F.m (eR F i)) : ℝ)
        - W.nu * F.Λ - 16 * ((7 : ℕ) : ℝ) ^ 2 * (e * ((Rset F).card : ℝ) + ∑ i, F.delta (eR F i))
        - 2 * ((7 : ℕ) : ℝ) * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)
      ≤ ∑ i, ∑ j, if i = j then (0 : ℝ)
          else (F.m (eR F i) : ℝ) * F.m (eR F j) * (Cg F (eR F i) (eR F j)) ^ 2 :=
  A2fix.agg_true_window_of_symm W (kPsi psiCos16) hcert kpsi_abs (fun i => F.x (eR F i))
    (F.x_mono.comp (eR F).strictMono) F.Λ_nonneg (fun i j => F.x_span _ _) (fun i => F.m (eR F i))
    (fun i => F.one_le_m _) ((Cg F).submatrix (eR F) (eR F)) (fun i j => Cg_abs_le_one F _ _)
    (fun i j => Cg_symm F _ _) (fun i => F.delta (eR F i)) (fun i => delta_nonneg F _) he0
    (fun i j _ => Cg_close F hke _ _)

/-! ### (5) bookkeeping -/

def P (i j : Fin F.n) : ℝ := (F.m i : ℝ) * F.m j * Cg F i j ^ 2
def PPt (i j : Fin F.n) : ℝ := if i = j then 0 else P F i j
def bet (i : Fin F.n) : ℝ := (if F.m i = 1 then (1 : ℝ) else 0) - 2 * F.m i * Cg F i i + (F.m i : ℝ) ^ 2 * Cg F i i ^ 2
def dgf (i : Fin F.n) : ℝ := ((F.m i : ℝ) * Cg F i i - 2) ^ 2

lemma P_symm (i j : Fin F.n) : P F i j = P F j i := by
  simp only [P, Cg_symm F i j]; ring

lemma cnt_T (p : ℕ → Prop) [DecidablePred p] :
    (#(univ.filter fun i : Fin (Tset F).card => p (F.m (eT F i))) : ℝ)
      = ∑ i ∈ Tset F, if p (F.m i) then (1 : ℝ) else 0 := by
  rw [natCast_card_filter]
  exact sum_orderEmb (Tset F) (fun i => if p (F.m i) then (1 : ℝ) else 0)

lemma cnt_R (p : ℕ → Prop) [DecidablePred p] :
    (#(univ.filter fun i : Fin (Rset F).card => p (F.m (eR F i))) : ℝ)
      = ∑ i ∈ Rset F, if p (F.m i) then (1 : ℝ) else 0 := by
  rw [natCast_card_filter]
  exact sum_orderEmb (Rset F) (fun i => if p (F.m i) then (1 : ℝ) else 0)

lemma sum_eR (g : Fin F.n → ℝ) : ∑ i, g (eR F i) = ∑ i ∈ Rset F, g i := sum_orderEmb _ _

lemma cnt_R2 : (∑ i ∈ Rset F, if 2 ≤ F.m i then (1 : ℝ) else 0) = ∑ i ∈ Rset F, if F.m i = 2 then (1 : ℝ) else 0 := by
  apply Finset.sum_congr rfl
  intro i hi
  rcases light_m F i (R_sub F hi) with h | h <;> simp [h]

lemma double_emb (S : Finset (Fin F.n)) (G : Fin F.n → Fin F.n → ℝ) :
    ∑ i : Fin S.card, ∑ j : Fin S.card, G (S.orderEmbOfFin rfl i) (S.orderEmbOfFin rfl j)
      = ∑ p ∈ S, ∑ q ∈ S, G p q := by
  rw [← sum_orderEmb S (fun p => ∑ q ∈ S, G p q)]
  exact Finset.sum_congr rfl fun i _ => sum_orderEmb S (G (S.orderEmbOfFin rfl i))

lemma E_R : (∑ i, ∑ j, if i = j then (0 : ℝ)
      else (F.m (eR F i) : ℝ) * F.m (eR F j) * (Cg F (eR F i) (eR F j)) ^ 2)
    = ∑ p ∈ Rset F, ∑ q ∈ Rset F, PPt F p q := by
  rw [← double_emb F (Rset F) (PPt F)]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  simp only [PPt, P]
  exact if_congr (eR F).injective.eq_iff.symm rfl rfl

lemma Y_T : (∑ i, ∑ j, (MY F i j) ^ 2) = ∑ p ∈ Tset F, ∑ q ∈ Rset F, P F p q := by
  rw [← sum_orderEmb (Tset F) (fun p => ∑ q ∈ Rset F, P F p q)]
  apply Finset.sum_congr rfl; intro i _
  rw [← sum_orderEmb (Rset F) (P F _)]
  apply Finset.sum_congr rfl; intro j _
  simp only [MY, submatrix_apply, Mf_sq, P]; rfl

lemma sum_diag_split {k : Type*} [Fintype k] [DecidableEq k] (X : k → k → ℝ) (c : ℝ) (a : k) :
    ∑ b, (X a b - if a = b then c else 0) ^ 2 = (X a a - c) ^ 2 + ∑ b, if a = b then 0 else X a b ^ 2 := by
  have h : ∀ b, (X a b - if a = b then c else 0) ^ 2
      = (if a = b then (X a b - c) ^ 2 else 0) + (if a = b then 0 else X a b ^ 2) := by
    intro b; split_ifs <;> simp
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma frob_T : frobSq (MT F - 2) = (∑ p ∈ Tset F, dgf F p) + ∑ p ∈ Tset F, ∑ q ∈ Tset F, PPt F p q := by
  rw [frobSq_eq_sum]
  have h1 : ∀ a b, (MT F - 2) a b = MT F a b - (if a = b then (2 : ℝ) else 0) := by
    intro a b; rw [Matrix.sub_apply, Matrix.ofNat_apply]; split_ifs <;> simp
  simp only [h1]
  rw [Finset.sum_congr rfl fun a _ => sum_diag_split (MT F) 2 a, Finset.sum_add_distrib]
  congr 1
  · rw [← sum_orderEmb (Tset F) (dgf F)]
    apply Finset.sum_congr rfl; intro a _
    simp only [MT, submatrix_apply, Mf_diag, dgf]; rfl
  · rw [← double_emb F (Tset F) (PPt F)]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp only [PPt, MT, submatrix_apply, Mf_sq, P]
    exact if_congr (eT F).injective.eq_iff.symm rfl rfl

lemma slack_light : F.slackOn F.light (F.sEq 1)
    = (∑ i ∈ F.light, bet F i) + ∑ i ∈ F.light, ∑ j ∈ F.light, PPt F i j := by
  set m' : Fin F.n → ℕ := fun i => if F.m i ≤ 2 then F.m i else 0 with hm'
  have hA1 := onslack_identity F.U m'
  have hd : diagonal (fun i => ((m' i : ℕ) : ℝ)) = diagonal (fun i => if i ∈ F.light then (F.m i : ℝ) else 0) := by
    congr 1; funext i; simp only [hm', light_iff]; split_ifs <;> simp
  have hc : #(univ.filter fun i => m' i = 1) = F.sEq 1 := by
    unfold ZeroFrame.sEq; congr 1
    apply Finset.filter_congr; intro i _
    simp only [hm']; split_ifs with h
    · exact Iff.rfl
    · constructor
      · intro h'; exact absurd h' (by norm_num)
      · intro h'; omega
  rw [hd, hc] at hA1
  unfold ZeroFrame.slackOn
  rw [hA1]
  have hL : ∀ g : Fin F.n → ℝ, ∑ i ∈ F.light, g i = ∑ i, if F.m i ≤ 2 then g i else 0 := by
    intro g; unfold ZeroFrame.light; rw [Finset.sum_filter]
  congr 1
  · rw [hL]; apply Finset.sum_congr rfl; intro i _
    simp only [hm', bet, Cg]; split_ifs with h1 h2 h2 <;> simp_all
  · rw [hL]; apply Finset.sum_congr rfl; intro i _
    rw [hL]
    split_ifs with h1
    · apply Finset.sum_congr rfl; intro j _
      simp only [hm', PPt, P, Cg]; split_ifs <;> simp_all
    · apply Finset.sum_eq_zero; intro j _
      simp only [hm']; split_ifs <;> simp_all

lemma PP_split : (∑ i ∈ F.light, ∑ j ∈ F.light, PPt F i j)
    = (∑ i ∈ Tset F, ∑ j ∈ Tset F, PPt F i j) + 2 * (∑ i ∈ Tset F, ∑ j ∈ Rset F, P F i j)
      + ∑ i ∈ Rset F, ∑ j ∈ Rset F, PPt F i j := by
  have hTR : (∑ i ∈ Tset F, ∑ j ∈ Rset F, PPt F i j) = ∑ i ∈ Tset F, ∑ j ∈ Rset F, P F i j := by
    apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj
    have : i ≠ j := fun h => Finset.disjoint_left.1 (TR_disj F) hi (h ▸ hj)
    simp [PPt, this]
  have hRT : (∑ i ∈ Rset F, ∑ j ∈ Tset F, PPt F i j) = ∑ i ∈ Tset F, ∑ j ∈ Rset F, P F i j := by
    rw [Finset.sum_comm, ← hTR]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
    simp only [PPt, P_symm F j i, eq_comm]
  rw [sum_light]
  simp only [sum_light F (fun j => PPt F _ j), Finset.sum_add_distrib]
  rw [hTR, hRT]; ring

lemma dg_bet {i : Fin F.n} (hi : i ∈ F.light) :
    dgf F i - bet F i = (if F.m i = 1 then (1 : ℝ) else 0) + 2 * F.m i * F.delta i := by
  simp only [dgf, bet, Cg_diag]
  rcases light_m F i hi with h | h <;> simp [h] <;> ring

lemma bet_R {i : Fin F.n} (hi : i ∈ F.light) : -(2 * F.m i * F.delta i) ≤ bet F i := by
  have hb := beta_bound (F.one_le_m i) (delta_nonneg F i) (delta_le_one F i)
  have hd := delta_nonneg F i
  simp only [bet, Cg_diag]
  rcases light_m F i hi with h | h <;> simp only [h] at hb ⊢ <;> norm_num at hb ⊢ <;> nlinarith

lemma sEq_split (j : ℕ) (hj : j ≤ 2) : (F.sEq j : ℝ)
    = (∑ i ∈ Tset F, if F.m i = j then (1 : ℝ) else 0) + ∑ i ∈ Rset F, if F.m i = j then (1 : ℝ) else 0 := by
  rw [← sum_light]
  unfold ZeroFrame.sEq
  rw [natCast_card_filter]
  symm
  apply Finset.sum_subset (subset_univ _)
  intro i _ hi
  rw [light_iff] at hi
  rw [if_neg (by omega)]

/-! ### (6) the per-height inequality -/

theorem oll_height {W : MarkWeights 7} (hcert : LocalCertAM (kPsi psiCos16) W)
    {β : ℝ} (hmaj : MajorantCert psiCos16 β) (hβ : β ≤ 33 / 10)
    (ha1 : W.a 0 = 1824837 / 10 ^ 8) (ha2 : W.a 1 = 1168069 / (5 * 10 ^ 7)) (hnu : W.nu = 3 / 250)
    {e e' : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1 / 20) (hke : ∀ t, |F.k t - kPsi psiCos16 t| ≤ e)
    (he'0 : 0 ≤ e') (he'1 : e' ≤ 1 / 40) (hdom : IsPosDefKernel (fun t => (1 + e') * kPsi psiCos16 t - F.k t))
    (hML : F.ML.IsHermitian) :
    trFun hML (kappaCh (2 - 2 * (1824837 / 10 ^ 8)))
      ≤ F.slackOn F.light (F.sEq 1) - 1824837 / 10 ^ 8 * (F.sEq 1 : ℝ) - 1168069 / (5 * 10 ^ 7) * (F.sEq 2 : ℝ)
        + 3 / 250 * F.Λ
        + (788 * ∑ i, (F.m i : ℝ) * F.delta i + 784 * e * F.n + 14 * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)) := by
  have hS := schur_step F hML cstar_bounds.1 (MR_eig F hmaj hβ he'0 he'1 hdom)
  rw [frob_T, Y_T] at hS
  have hT := tight_part F he0 he1 hke
  have hR := agg_R F hcert he0 hke
  rw [cnt_R F (· = 1), cnt_R F (2 ≤ ·), cnt_R2, E_R, ha1, ha2, hnu,
    sum_eR F F.delta] at hR
  have hsl := slack_light F
  rw [sum_light F (bet F), PP_split] at hsl
  have hdg : (∑ i ∈ Tset F, dgf F i) - (∑ i ∈ Tset F, bet F i)
      = (∑ i ∈ Tset F, if F.m i = 1 then (1 : ℝ) else 0) + ∑ i ∈ Tset F, 2 * F.m i * F.delta i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => dg_bet F (T_sub F hi)
  have hbR : -(∑ i ∈ Rset F, 2 * F.m i * F.delta i) ≤ ∑ i ∈ Rset F, bet F i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i hi => bet_R F (R_sub F hi)
  have hs1 := sEq_split F 1 (by norm_num)
  have hs2 := sEq_split F 2 (by norm_num)
  have hdR : (∑ i ∈ Rset F, F.delta i) ≤ ∑ i ∈ Rset F, (F.m i : ℝ) * F.delta i := by
    apply Finset.sum_le_sum; intro i _
    have := delta_nonneg F i; have : (1 : ℝ) ≤ F.m i := by exact_mod_cast F.one_le_m i
    nlinarith
  have hmd : ∀ i, 0 ≤ (F.m i : ℝ) * F.delta i := fun i => mul_nonneg (Nat.cast_nonneg _) (delta_nonneg F i)
  have hDTR : (∑ i ∈ Tset F, (F.m i : ℝ) * F.delta i) + (∑ i ∈ Rset F, (F.m i : ℝ) * F.delta i)
      ≤ ∑ i, (F.m i : ℝ) * F.delta i := by
    rw [← sum_light]; exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hmd i
  have hDR0 : 0 ≤ ∑ i ∈ Rset F, (F.m i : ℝ) * F.delta i := Finset.sum_nonneg fun i _ => hmd i
  have hDT0 : 0 ≤ ∑ i ∈ Tset F, (F.m i : ℝ) * F.delta i := Finset.sum_nonneg fun i _ => hmd i
  have h2T : (∑ i ∈ Tset F, 2 * (F.m i : ℝ) * F.delta i) = 2 * ∑ i ∈ Tset F, (F.m i : ℝ) * F.delta i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have h2R : (∑ i ∈ Rset F, 2 * (F.m i : ℝ) * F.delta i) = 2 * ∑ i ∈ Rset F, (F.m i : ℝ) * F.delta i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hr : e * ((Rset F).card : ℝ) ≤ e * F.n := by
    apply mul_le_mul_of_nonneg_left _ he0
    exact_mod_cast (card_le_univ (Rset F)).trans (by simp)
  have hB : 0 ≤ (∑ i, |W.b i 0|) + ∑ i, |W.b i 1| := by positivity
  push_cast at hR
  linarith

end OLL
end ZetaS

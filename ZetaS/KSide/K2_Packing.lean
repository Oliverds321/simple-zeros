/-
Node K2 (track K) — prop:zeta-pack (l.394–423), weighted form (lem:zeta-Dprime), CORRECTED STATEMENT (L4_1, 28 Sep 2026).

The skeleton statement `packing` is FALSE as written when S = 0: the hypothesis `∀ i j, y j − y i ≤ Λ` is then vacuous and
Λ may be negative, while tr Ψ of the empty matrix is 0. Counterexample: K = 2, γ₁,₀ = 2, μ₀ = 1 (ν = 1), k ≡ 1
(positive definite, even, k(0) = 1), c = 2 (F(g) = g + 2 ≥ 2), m = 2 (A = 2 = m/(m − 1), B = Φ₂(2) = 2, τ = 1/2),
S = 0, Λ = −10: the right side is 0 − 4 − (2/2)(1/2)(−10) = 1 > 0 = tr Ψ(G).
Fix: add `hΛ0 : 0 ≤ Λ` (automatic when S ≥ 1; in every use Λ = GramData.Λ ≥ 0).

"tr Ψ(G) ≥ (B/m)S − 2B − (B/A)τΛ",  A = c(m − K + 1), B = Φ_m(A), τ = ν(m − K + 1)/m.

Proof (the draft's, with the offset average done exactly): for every start a ∈ [0, S − m] the block G_a of m consecutive
points has unit diagonal, so tr Ψ(G_a) ≥ Φ_m(E_a) (L3) ≥ (B/A)·min(E_a, A) (L3b) ≥ B − (B/A)P_a with E_a ≥ A − P_a (K1).
For an offset o < m the blocks with a ≡ o (mod m) are disjoint, so pinching (L4, `KHelp.pinch_blocks`) gives
tr Ψ(G) ≥ Σ_{a ≡ o} tr Ψ(G_a); summing over o, m·tr Ψ(G) ≥ Σ_a tr Ψ(G_a) ≥ (S − m + 1)B − (B/A)Σ_a P_a, and
Σ_a P_a ≤ ν(m − K + 1)Λ (each gap is counted at most once per (window, position) pair). Level A.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L3_PhiM
import ZetaS.LinAlg.L3b_PhiM_props
import ZetaS.SigmaDist.A2_AggTrueWindow
import ZetaS.KSide.K1_LocalToBlock
import ZetaS.KSide.KHelpers

open Matrix RHLinalg Finset

namespace ZetaS

namespace K2aux

lemma PhiM_nonneg {m : ℕ} (hm : 2 ≤ m) {A : ℝ} (hA : 0 ≤ A) : 0 ≤ PhiM m A := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  unfold PhiM
  split_ifs with h
  · exact hA
  · push_neg at h
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    have hx : 1 < ((m : ℝ) - 1) * A / m := by
      rw [lt_div_iff₀ (by linarith)]
      rw [div_lt_iff₀ hm1] at h
      nlinarith
    have hs := Real.sq_sqrt (by linarith : (0 : ℝ) ≤ ((m : ℝ) - 1) * A / m)
    have hs1 : 1 < Real.sqrt (((m : ℝ) - 1) * A / m) := by
      rw [Real.lt_sqrt (by norm_num)]; linarith
    have hAm : ((m : ℝ) - 1) * A / m ≤ A := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith

/-- a strictly increasing extension of `y : Fin S → ℝ` to `ℕ`. -/
noncomputable def ext {S : ℕ} (hS : 1 ≤ S) (y : Fin S → ℝ) (p : ℕ) : ℝ :=
  if h : p < S then y ⟨p, h⟩ else y ⟨S - 1, by omega⟩ + ((p : ℝ) - ((S - 1 : ℕ) : ℝ))

lemma ext_lt {S : ℕ} (hS : 1 ≤ S) (y : Fin S → ℝ) {p : ℕ} (hp : p < S) : ext hS y p = y ⟨p, hp⟩ := by
  simp [ext, hp]

lemma ext_strictMono {S : ℕ} (hS : 1 ≤ S) {y : Fin S → ℝ} (hy : StrictMono y) : StrictMono (ext hS y) := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases h1 : n + 1 < S
  · rw [ext_lt hS y (by omega : n < S), ext_lt hS y h1]
    exact hy (Fin.mk_lt_mk.2 (by omega))
  · by_cases h2 : n < S
    · have hn : n = S - 1 := by omega
      rw [ext_lt hS y h2]
      simp only [ext, dif_neg h1]
      have : (y ⟨n, h2⟩ : ℝ) = y ⟨S - 1, by omega⟩ := by congr 1; exact Fin.ext hn
      rw [this]
      have : ((n + 1 : ℕ) : ℝ) - ((S - 1 : ℕ) : ℝ) = 1 := by rw [← hn]; push_cast; ring
      rw [this]; linarith
    · simp only [ext, dif_neg h1, dif_neg h2]
      push_cast; linarith

end K2aux

open K2aux in
theorem packing_fix {K : ℕ} (W : LocalWeights K) (k : ℝ → ℝ) (hk0 : k 0 = 1) (hkev : ∀ t, k (-t) = k t)
    (hkpd : IsPosDefKernel k) {c : ℝ} (hc : 0 < c) (hLI : LocalCert k W c)
    {S : ℕ} (y : Fin S → ℝ) (hy : StrictMono y) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ i j, y j - y i ≤ Λ)
    {m : ℕ} (hKm : K ≤ m) :
    PhiM m (c * ((m : ℝ) - K + 1)) / m * S - 2 * PhiM m (c * ((m : ℝ) - K + 1))
        - PhiM m (c * ((m : ℝ) - K + 1)) / (c * ((m : ℝ) - K + 1))
          * (W.nu * ((m : ℝ) - K + 1) / m) * Λ
      ≤ trFun (hkpd S y).isHermitian Psi := by
  classical
  have hK2 : 2 ≤ K := W.two_le
  have hm2 : 2 ≤ m := le_trans hK2 hKm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hKmR : (K : ℝ) ≤ m := by exact_mod_cast hKm
  set A := c * ((m : ℝ) - K + 1) with hAdef
  set B := PhiM m A with hBdef
  have hA : 0 < A := mul_pos hc (by linarith)
  have hB0 : 0 ≤ B := PhiM_nonneg hm2 hA.le
  have hnu : 0 ≤ W.nu := Finset.sum_nonneg fun l _ => W.μ_nonneg l
  have hG := hkpd S y
  have htr0 : 0 ≤ trFun hG.isHermitian Psi := KHelp.trFun_nonneg hG (fun x _ => KHelp.psi_nonneg x)
  have hpen0 : 0 ≤ B / A * (W.nu * ((m : ℝ) - K + 1) / m) * Λ := by
    apply mul_nonneg _ hΛ0
    apply mul_nonneg (div_nonneg hB0 hA.le)
    apply div_nonneg (mul_nonneg hnu (by linarith)) (by linarith)
  -- short configurations
  by_cases hSm : S < m
  · have : B / m * S ≤ B := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      have : (S : ℝ) ≤ m := by exact_mod_cast hSm.le
      nlinarith
    linarith
  push_neg at hSm
  have hS1 : 1 ≤ S := le_trans (by omega) hSm
  set Y := ext hS1 y with hYdef
  have hYmono : StrictMono Y := ext_strictMono hS1 hy
  -- blocks
  let e : ℕ → Fin m → Fin S := fun a j => ⟨min (a + j) (S - 1), by omega⟩
  have he : ∀ a ∈ range (S - m + 1), ∀ j : Fin m, ((e a j : Fin S) : ℕ) = a + j := by
    intro a ha j
    have := Finset.mem_range.1 ha; have := j.isLt
    show min (a + j) (S - 1) = a + j
    exact min_eq_left (by omega)
  have hYe : ∀ a ∈ range (S - m + 1), ∀ j : Fin m, Y (a + j) = y (e a j) := by
    intro a ha j
    have h := he a ha j
    have hlt : a + j < S := by rw [← h]; exact (e a j).isLt
    rw [hYdef, ext_lt hS1 y hlt]; congr 1; exact Fin.ext h.symm
  -- penalty of block a
  let P : ℕ → ℝ := fun a => ∑ t ∈ range (m - K + 1), ∑ l : Fin (K - 1),
    W.μ l * (Y (a + (t + l + 1)) - Y (a + (t + l)))
  have hP0 : ∀ a, 0 ≤ P a := by
    intro a
    apply Finset.sum_nonneg; intro t _; apply Finset.sum_nonneg; intro l _
    exact mul_nonneg (W.μ_nonneg l) (sub_nonneg.2 (hYmono.monotone (by omega)))
  -- (1) one block
  have hblock : ∀ a ∈ range (S - m + 1),
      B - B / A * P a ≤ trFun (hG.submatrix (e a)).isHermitian Psi := by
    intro a ha
    set Ga := (kerMat k y).submatrix (e a) (e a) with hGa
    have hdiag : ∀ i, Ga i i = 1 := by intro i; simp [hGa, kerMat, hk0]
    have hL3 := trPsi_ge_PhiM (hG.submatrix (e a)) hdiag
    -- the energy of block a
    have hE : frobSq (Ga - 1) = ∑ i ∈ range m, ∑ j ∈ range m,
        if i = j then (0 : ℝ) else k (Y (a + i) - Y (a + j)) ^ 2 := by
      rw [KHelp.frobSq_eq_sum]
      rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range m,
        if i = j then (0 : ℝ) else k (Y (a + i) - Y (a + j)) ^ 2)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) = j then (0 : ℝ) else k (Y (a + i) - Y (a + j)) ^ 2)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hYe a ha i, hYe a ha j]
      by_cases hij : i = j
      · subst hij; simp [hGa, kerMat, hk0]
      · have : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
        simp [hGa, kerMat, hij, this, Matrix.one_apply_ne hij]
    have hK1 := local_to_block W k hkev hLI hKm (fun p => Y (a + p))
      (hYmono.comp (strictMono_id.const_add a))
    have hEA : A - P a ≤ frobSq (Ga - 1) := by rw [hE]; linarith
    have hE0 : 0 ≤ frobSq (Ga - 1) := by rw [KHelp.frobSq_eq_sum]; positivity
    have hch := PhiM_ge_chord hm2 hA hE0
    have hmin : A - P a ≤ min (frobSq (Ga - 1)) A := le_min hEA (by linarith [hP0 a])
    have h1 : B / A * (A - P a) ≤ B / A * min (frobSq (Ga - 1)) A :=
      mul_le_mul_of_nonneg_left hmin (div_nonneg hB0 hA.le)
    have h2 : B / A * (A - P a) = B - B / A * P a := by field_simp
    linarith
  -- (2) pinching for each offset, then sum over the offsets
  have hpinch : ∀ o ∈ range m, ∑ a ∈ (range (S - m + 1)).filter (fun a => a % m = o),
      trFun (hG.submatrix (e a)).isHermitian Psi ≤ trFun hG.isHermitian Psi := by
    intro o _
    apply KHelp.pinch_blocks hG _ e
    · intro a ha i j hij
      have ha' := (Finset.mem_filter.1 ha).1
      have := he a ha' i; have := he a ha' j
      apply Fin.ext; have := congrArg Fin.val hij; omega
    · intro a ha b hb i j hij
      obtain ⟨ha', hao⟩ := Finset.mem_filter.1 ha
      obtain ⟨hb', hbo⟩ := Finset.mem_filter.1 hb
      have h1 := he a ha' i; have h2 := he b hb' j
      have hv : a + i = b + j := by rw [← h1, ← h2, hij]
      have hab : a ≡ b [MOD m] := by unfold Nat.ModEq; rw [hao, hbo]
      have hij' : (i : ℕ) ≡ j [MOD m] := Nat.ModEq.add_left_cancel hab (by rw [hv])
      have : (i : ℕ) = j := by
        unfold Nat.ModEq at hij'
        rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hij'
      omega
    · exact KHelp.psi_convexOn
    · exact fun x _ => KHelp.psi_nonneg x
  have hsumo : ∑ o ∈ range m, ∑ a ∈ (range (S - m + 1)).filter (fun a => a % m = o),
      trFun (hG.submatrix (e a)).isHermitian Psi
        = ∑ a ∈ range (S - m + 1), trFun (hG.submatrix (e a)).isHermitian Psi :=
    Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_range.2 (Nat.mod_lt a (by omega))) _
  have hm_tr : ∑ a ∈ range (S - m + 1), trFun (hG.submatrix (e a)).isHermitian Psi
      ≤ (m : ℝ) * trFun hG.isHermitian Psi := by
    rw [← hsumo]
    have := Finset.sum_le_sum hpinch
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    exact this
  -- (3) the penalties
  have hpen : ∑ a ∈ range (S - m + 1), P a ≤ W.nu * ((m : ℝ) - K + 1) * Λ := by
    let g : ℕ → ℝ := fun j => Y (j + 1) - Y j
    have hg0 : ∀ j, 0 ≤ g j := fun j => sub_nonneg.2 (hYmono.monotone (by omega))
    have htel : ∑ j ∈ range (S - 1), g j ≤ Λ := by
      rw [Finset.sum_range_sub (fun j => Y j)]
      rw [hYdef, ext_lt hS1 y (by omega : S - 1 < S), ext_lt hS1 y (by omega : 0 < S)]
      exact hΛ _ _
    have hinner : ∀ t ∈ range (m - K + 1), ∀ l : Fin (K - 1),
        ∑ a ∈ range (S - m + 1), g (a + (t + l)) ≤ Λ := by
      intro t ht l
      have ht' := Finset.mem_range.1 ht; have hl := l.isLt
      refine le_trans ?_ htel
      have := A2fix.sum_shift_le g hg0 (L := S - m + 1) (i := t + l) (N := S - 1) (fun a ha => by omega)
      exact this
    calc ∑ a ∈ range (S - m + 1), P a
        = ∑ t ∈ range (m - K + 1), ∑ l : Fin (K - 1), W.μ l * ∑ a ∈ range (S - m + 1), g (a + (t + l)) := by
          simp only [P]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [g]; congr 3 <;> ring
      _ ≤ ∑ t ∈ range (m - K + 1), ∑ l : Fin (K - 1), W.μ l * Λ := by
          apply Finset.sum_le_sum; intro t ht; apply Finset.sum_le_sum; intro l _
          exact mul_le_mul_of_nonneg_left (hinner t ht l) (W.μ_nonneg l)
      _ = W.nu * ((m : ℝ) - K + 1) * Λ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_mul]
          unfold LocalWeights.nu
          rw [Nat.cast_add, Nat.cast_sub hKm]; push_cast; ring
  -- (4) assemble
  have hsumB : ∑ a ∈ range (S - m + 1), (B - B / A * P a)
      ≤ ∑ a ∈ range (S - m + 1), trFun (hG.submatrix (e a)).isHermitian Psi :=
    Finset.sum_le_sum hblock
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum] at hsumB
  have hcnt : ((S - m + 1 : ℕ) : ℝ) = (S : ℝ) - m + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hSm]; push_cast; ring
  rw [hcnt] at hsumB
  have hBA : B / A * ∑ a ∈ range (S - m + 1), P a ≤ B / A * (W.nu * ((m : ℝ) - K + 1) * Λ) :=
    mul_le_mul_of_nonneg_left hpen (div_nonneg hB0 hA.le)
  have hm0 : (0 : ℝ) < m := by linarith
  have key : (m : ℝ) * (B / m * S - 2 * B - B / A * (W.nu * ((m : ℝ) - K + 1) / m) * Λ)
      ≤ (m : ℝ) * trFun hG.isHermitian Psi := by
    have e1 : (m : ℝ) * (B / m * S - 2 * B - B / A * (W.nu * ((m : ℝ) - K + 1) / m) * Λ)
        = B * S - 2 * m * B - B / A * (W.nu * ((m : ℝ) - K + 1) * Λ) := by
      field_simp
    rw [e1]
    nlinarith
  exact le_of_mul_le_mul_left key hm0

end ZetaS

namespace ZetaS

/-- **Node K2 (prop:zeta-pack)** under the node's original name `packing`, with the statement change ACCEPTED by the lead (28 Sep 2026):
the statement of `packing_fix` (`0 ≤ Λ`); the skeleton statement is withdrawn. Integrated by L0_1. -/
alias packing := packing_fix

end ZetaS

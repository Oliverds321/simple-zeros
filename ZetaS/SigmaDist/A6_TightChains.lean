/-
Node A6 (track K/P, all-marks) — lem:sigd-tight (sec_zeta.tex l.1299–1318), STATEMENT written by L2_2 (28 Sep 2026;
there was no Lean statement in v1 or v2; adopted by the lead 28 Sep with the hypotheses μ(k*) ≥ 0, a₁, a₂ ≥ 0), abstract form:

"Let 𝒯 ⊂ 𝒪_L be a union of n_ch maximal tight chains (maximal runs of consecutive sites with consecutive gaps < 3/4; each
has ≥ 2 sites), and k_* := k_ψ(3/4) − ε_T. Then
  Δ_𝒯 := tr(2I − M_𝒯)₊² − (1 + a₁)s₁(𝒯) − a₂s₂(𝒯) ≥ n_ch(μ(k_*) − max(a₁, a₂)),
μ(k) := min{2k² − 2a₁, 4k² − 2a₂, (1/2 + (1/4 + 2k²)^{1/2})² − 1 − a₁ − a₂}."

Abstract reading (what A7 has at hand, with 𝒯's sites in ordinate order):
  * sites `x` strictly increasing; every site has an index-neighbour at distance < 3/4 (chains have ≥ 2 sites);
    chains = maximal runs with consecutive gaps < 3/4; `nChains x` = number of chain starts;
  * marks `m ∈ {1, 2}`; true matrix `M_𝒯 = (√(m m′)(k_φ(x − x′) − Ê))`, with `Ê ⪰ 0` and `K^φ − Ê ⪰ 0` (it is a Gram matrix);
  * `k_φ(0) = 1`, `|k_φ| ≤ 1`, even, and `k_φ ≥ k_*` on [0, 3/4) — this packages "k_ψ decreasing on [0,1] (N3),
    |k_φ − k_ψ| ≤ ε_T (lem:sigd-residue (iii))";
  * two hypotheses the draft leaves implicit: `μ(k_*) ≥ 0` and `a₁, a₂ ≥ 0` (without μ(k_*) ≥ 0 the draft's lemma is false:
    one chain of 6 simple sites, k_φ = 1_{0}, Ê = 0, k_* = 0 gives −6a₁ < −3a₂).
Numerical test: py/numtest_A6.py.

PROOF (L2_2, round 3): pinching L4 (`trFun_pinch`, L2_1) with the greedy partition of each chain into consecutive pairs and
at most one trailing singleton (`secB`: a site is the second of a pair iff its left gap is tight and its left neighbour is
not itself a second); the pair blocks are reindexed to `Fin 2` (trFun is invariant: same characteristic polynomial) and
bounded by the Weyl-free block lemmas of A6_BlockBounds (marks (1,1), (2,2), (1,2)/(2,1)); singletons cost ≥ −max(a₁,a₂);
counting: chain starts ⊆ pair leaders, and singleton leaders inject into chain starts.
-/
import ZetaS.Interfaces
import ZetaS.LinAlg.L4_Pinching
import ZetaS.SigmaDist.A6_BlockBounds

open Matrix Finset RHLinalg

namespace ZetaS

/-- `μ(k)` of lem:sigd-tight. -/
noncomputable def muTight (a₁ a₂ k : ℝ) : ℝ :=
  min (min (2 * k ^ 2 - 2 * a₁) (4 * k ^ 2 - 2 * a₂))
    ((1 / 2 + Real.sqrt (1 / 4 + 2 * k ^ 2)) ^ 2 - 1 - a₁ - a₂)

/-- number of maximal tight chains of an increasing site list: the sites whose left index-neighbour (if any) is at
distance ≥ 3/4. -/
noncomputable def nChains {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  #(univ.filter fun i : Fin n => ∀ j : Fin n, j.val + 1 = i.val → 3 / 4 ≤ x i - x j)

namespace A6pf

open A6aux

/-! ### spectral bookkeeping -/

lemma trFun_eq_roots {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : trFun hA f = (A.charpoly.roots.map f).sum := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  unfold trFun
  rw [Finset.sum_eq_multiset_sum]
  congr 1

lemma trFun_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (e : κ ≃ ι) (hB : (A.submatrix e e).IsHermitian) (f : ℝ → ℝ) :
    trFun hB f = trFun hA f := by
  rw [trFun_eq_roots, trFun_eq_roots]
  have : (A.submatrix e e).charpoly = A.charpoly := by
    have h := Matrix.charpoly_reindex e.symm A
    rwa [Matrix.reindex_apply, Equiv.symm_symm] at h
  rw [this]

lemma trFun_single {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (p : ι)
    (hu : (univ : Finset ι) = {p}) (f : ℝ → ℝ) : trFun hA f = f (A p p) := by
  have h := rtrace_eq_sum_eigenvalues hA
  rw [hu, Finset.sum_singleton] at h
  unfold trFun
  rw [hu, Finset.sum_singleton, ← h]
  simp [rtrace, Matrix.trace, hu]

lemma trFun_empty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) : trFun hA f = 0 := by
  unfold trFun; simp

lemma psd_entry_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) :
    A i j ^ 2 ≤ A i i * A j j := by
  have h := (hA.submatrix ![i, j]).det_nonneg
  rw [Matrix.det_fin_two] at h
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hs : A j i = A i j := by
    have := hA.isHermitian.apply j i
    simpa using this.symm
  rw [hs] at h
  nlinarith

lemma fT_convex : ConvexOn ℝ (Set.Ici 0) fT := by
  have h1 : ConvexOn ℝ (Set.Ici (0 : ℝ)) ((fun _ => (2 : ℝ)) - id) :=
    (convexOn_const 2 (convex_Ici 0)).sub (concaveOn_id (convex_Ici 0))
  have h2 := h1.sup (convexOn_const 0 (convex_Ici 0))
  have h3 := h2.pow (fun t _ => le_sup_right) 2
  refine h3.congr ?_
  intro t _
  simp only [fT, Pi.pow_apply, Pi.sup_apply, Pi.sub_apply, id]

/-! ### the greedy pairing -/

/-- tight left-to-right gap after position `i`. -/
noncomputable def tB {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : Bool := by
  classical exact decide (∃ h : i + 1 < n, x ⟨i + 1, h⟩ - x ⟨i, Nat.lt_of_succ_lt h⟩ < 3 / 4)

lemma tB_iff {n : ℕ} (x : Fin n → ℝ) (i : ℕ) :
    tB x i = true ↔ ∃ h : i + 1 < n, x ⟨i + 1, h⟩ - x ⟨i, Nat.lt_of_succ_lt h⟩ < 3 / 4 := by
  unfold tB; simp

/-- `secB t i`: position `i` is the second member of a pair. -/
def secB (t : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => t i && !secB t i

lemma secB_succ (t : ℕ → Bool) (i : ℕ) : secB t (i + 1) = (t i && !secB t i) := rfl

/-- block label: a second is attached to its left neighbour. -/
def blkF {n : ℕ} (s : ℕ → Bool) (i : Fin n) : Fin n :=
  if s i.val then ⟨i.val - 1, by omega⟩ else i

lemma blk_eq_iff {n : ℕ} (t : ℕ → Bool) (i b : Fin n) :
    blkF (secB t) i = b ↔ (secB t i.val = false ∧ i = b) ∨ (secB t i.val = true ∧ i.val = b.val + 1) := by
  unfold blkF
  cases hs : secB t i.val
  · simp
  · have hi : i.val ≠ 0 := by intro h0; rw [h0] at hs; simp [secB] at hs
    simp only [if_true, Bool.true_eq_false, false_and, true_and, false_or]
    constructor
    · intro h; rw [← h]; simp; omega
    · intro h; ext; simp; omega

end A6pf

open A6pf A6aux

set_option maxHeartbeats 1000000 in
theorem tight_chains {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x)
    (hchain : ∀ i : Fin n, ∃ j : Fin n, (j.val + 1 = i.val ∨ i.val + 1 = j.val) ∧ |x i - x j| < 3 / 4)
    (m : Fin n → ℕ) (hm : ∀ i, m i = 1 ∨ m i = 2)
    (kφ : ℝ → ℝ) (hk0 : kφ 0 = 1) (hk1 : ∀ t, |kφ t| ≤ 1) (hkeven : ∀ t, kφ (-t) = kφ t)
    {kstar : ℝ} (hkstar0 : 0 ≤ kstar) (hkstar : ∀ t, 0 ≤ t → t < 3 / 4 → kstar ≤ kφ t)
    (E : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosSemidef) (hKE : (kerMat kφ x - E).PosSemidef)
    {a₁ a₂ : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hμ : 0 ≤ muTight a₁ a₂ kstar)
    (hM : (Matrix.of fun i j => Real.sqrt ((m i : ℝ) * m j) * (kerMat kφ x - E) i j).IsHermitian) :
    (nChains x : ℝ) * (muTight a₁ a₂ kstar - max a₁ a₂)
      ≤ trFun hM (fun t => (max (2 - t) 0) ^ 2) - ∑ i, (if m i = 1 then 1 + a₁ else a₂) := by
  classical
  set G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => Real.sqrt ((m i : ℝ) * m j) * (kerMat kφ x - E) i j
    with hGdef
  set c : Fin n → ℝ := fun i => if m i = 1 then 1 + a₁ else a₂ with hc
  set μ := muTight a₁ a₂ kstar with hμdef
  set A := max a₁ a₂ with hA
  have hA0 : 0 ≤ A := le_trans ha₁ (le_max_left _ _)
  -- G ⪰ 0
  have hmv : ∀ i, (0 : ℝ) ≤ m i := fun i => Nat.cast_nonneg _
  have hG : G.PosSemidef := by
    have h := hKE.mul_mul_conjTranspose_same (diagonal fun i => Real.sqrt (m i))
    have e : diagonal (fun i => Real.sqrt (m i)) * (kerMat kφ x - E) * (diagonal fun i => Real.sqrt (m i))ᴴ = G := by
      ext i j
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.diagonal_transpose, Matrix.mul_diagonal,
        Matrix.diagonal_mul]
      simp only [hGdef, Matrix.of_apply]
      rw [Real.sqrt_mul (hmv i)]; ring
    rwa [e] at h
  -- entries of G
  have hGd : ∀ i, G i i = m i * (1 - E i i) := by
    intro i
    simp only [hGdef, Matrix.of_apply, Matrix.sub_apply, kerMat, sub_self, hk0]
    rw [Real.sqrt_mul_self (hmv i)]
  have hGo : ∀ i j, G i j = Real.sqrt ((m i : ℝ) * m j) * (kφ (x i - x j) - E i j) := by
    intro i j; simp only [hGdef, Matrix.of_apply, Matrix.sub_apply, kerMat]
  have hδ0 : ∀ i, 0 ≤ E i i := fun i => hE.diag_nonneg
  have hδ1 : ∀ i, E i i ≤ 1 := by
    intro i
    have := hKE.diag_nonneg (i := i)
    simp only [Matrix.sub_apply, kerMat, Matrix.of_apply, sub_self, hk0] at this
    linarith
  have hEsq : ∀ i j, E i j ^ 2 ≤ E i i * E j j := fun i j => psd_entry_sq hE i j
  have hKEsq : ∀ i j, (kφ (x i - x j) - E i j) ^ 2 ≤ (1 - E i i) * (1 - E j j) := by
    intro i j
    have := psd_entry_sq hKE i j
    simpa only [Matrix.sub_apply, kerMat, Matrix.of_apply, sub_self, hk0] using this
  -- the partition
  set t := tB x with ht
  set blk : Fin n → Fin n := blkF (secB t) with hblk
  -- pinching
  have hpinch := trFun_pinch hG blk fT_convex
  have hTM : trFun hM (fun t => (max (2 - t) 0) ^ 2) = trFun hG.isHermitian fT := rfl
  -- claims by blocks
  have hclaims : ∑ i, c i = ∑ b, ∑ i : {i // blk i = b}, c i := (Fintype.sum_fiberwise blk c).symm
  -- per-block value
  set w : Fin n → ℝ := fun b => if secB t b.val then 0 else if secB t (b.val + 1) then μ else -A with hw
  have hblock : ∀ b : Fin n, w b ≤ trFun ((hG.submatrix (fun i : {i // blk i = b} => (i : Fin n))).isHermitian) fT
      - ∑ i : {i // blk i = b}, c i := by
    intro b
    by_cases hsb : secB t b.val = true
    · -- no member
      have hemp : IsEmpty {i // blk i = b} := by
        refine ⟨fun ⟨i, hi⟩ => ?_⟩
        rcases (blk_eq_iff t i b).1 hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2] at h1; rw [h1] at hsb; exact Bool.false_ne_true hsb
        · rw [h2, secB_succ, hsb] at h1; simp at h1
      simp only [hw, hsb, if_true]
      rw [trFun_empty]; simp
    · have hsb' : secB t b.val = false := by simpa using hsb
      by_cases hs1 : secB t (b.val + 1) = true
      · -- pair block {b, b+1}
        have htb : t b.val = true := by
          rw [secB_succ] at hs1; simp at hs1; exact hs1.1
        obtain ⟨hb1, hgap⟩ := (tB_iff x b.val).1 htb
        set b1 : Fin n := ⟨b.val + 1, hb1⟩
        have hmem : ∀ i : Fin n, blk i = b ↔ i = b ∨ i = b1 := by
          intro i
          rw [blk_eq_iff]
          constructor
          · rintro (⟨_, h⟩ | ⟨_, h⟩)
            · exact Or.inl h
            · exact Or.inr (Fin.ext h)
          · rintro (h | h)
            · exact Or.inl ⟨h ▸ hsb', h⟩
            · refine Or.inr ⟨?_, ?_⟩
              · rw [h]; exact hs1
              · rw [h]
        have hbb1 : b ≠ b1 := by intro h; have := congrArg Fin.val h; simp [b1] at this
        set p : {i // blk i = b} := ⟨b, (hmem b).2 (Or.inl rfl)⟩
        set q : {i // blk i = b} := ⟨b1, (hmem b1).2 (Or.inr rfl)⟩
        have hpq : p ≠ q := by intro h; exact hbb1 (congrArg Subtype.val h)
        have hu : ∀ y : {i // blk i = b}, y = p ∨ y = q := by
          intro y
          rcases (hmem y.1).1 y.2 with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        -- the claims of the block
        have hcl : ∑ i : {i // blk i = b}, c i = c b + c b1 := by
          have huniv : (univ : Finset {i // blk i = b}) = {p, q} := by
            ext y; simp only [mem_univ, true_iff, mem_insert, mem_singleton]; exact hu y
          rw [huniv, Finset.sum_pair hpq]
        -- reindex to Fin 2 in a chosen order
        have reidx : ∀ (u v : {i // blk i = b}), u ≠ v → (∀ y, y = u ∨ y = v) →
            ∃ X : Matrix (Fin 2) (Fin 2) ℝ, ∃ hX : X.IsHermitian,
              trFun ((hG.submatrix (fun i : {i // blk i = b} => (i : Fin n))).isHermitian) fT = trFun hX fT ∧
              X 0 0 = G u u ∧ X 1 1 = G v v ∧ X 0 1 = G u v := by
          intro u v huv huv'
          have hinj : Function.Injective (![u, v] : Fin 2 → {i // blk i = b}) := by
            intro a a' h
            fin_cases a <;> fin_cases a' <;> simp_all [Ne.symm huv]
          have hsurj : Function.Surjective (![u, v] : Fin 2 → {i // blk i = b}) := by
            intro y
            rcases huv' y with h | h
            · exact ⟨0, by simp [h]⟩
            · exact ⟨1, by simp [h]⟩
          set e := Equiv.ofBijective _ ⟨hinj, hsurj⟩
          set G' := G.submatrix (fun i : {i // blk i = b} => (i : Fin n)) (fun i : {i // blk i = b} => (i : Fin n))
          have hX : (G'.submatrix e e).IsHermitian := (hG.submatrix _).isHermitian.submatrix e
          refine ⟨G'.submatrix e e, hX, (trFun_submatrix_equiv _ e hX fT).symm, ?_, ?_, ?_⟩ <;> rfl
        -- block parameters
        have hκ : (kφ (x b - x b1)) = kφ (x b1 - x b) := by rw [← hkeven, neg_sub]
        have hgap' : x b1 - x b < 3 / 4 := hgap
        have hpos : 0 ≤ x b1 - x b := by
          have : b < b1 := by rw [Fin.lt_def]; simp [b1]
          exact sub_nonneg.2 (hx this).le
        have hκs : kstar ≤ (kφ (x b - x b1)) := by rw [hκ]; exact hkstar _ hpos hgap'
        have hκ0 : 0 ≤ (kφ (x b - x b1)) := le_trans hkstar0 hκs
        have hκ1 : (kφ (x b - x b1)) ≤ 1 := le_trans (le_abs_self _) (hk1 _)
        have hκ2 : kstar ^ 2 ≤ (kφ (x b - x b1)) ^ 2 := pow_le_pow_left₀ hkstar0 hκs 2
        have hee : (E b b1) ^ 2 ≤ (E b b) * (E b1 b1) := hEsq b b1
        have hee' : |(E b b1)| ≤ ((E b b) + (E b1 b1)) / 2 := by
          have h1 := hδ0 b; have h2 := hδ0 b1
          nlinarith [sq_abs (E b b1), abs_nonneg (E b b1), sq_nonneg ((E b b) - (E b1 b1))]
        have hpsd : ((kφ (x b - x b1)) - (E b b1)) ^ 2 ≤ (1 - (E b b)) * (1 - (E b1 b1)) := hKEsq b b1
        have hGbb1 : G b b1 = Real.sqrt ((m b : ℝ) * m b1) * ((kφ (x b - x b1)) - (E b b1)) := hGo b b1
        have hGb1b : G b1 b = Real.sqrt ((m b1 : ℝ) * m b) * (kφ (x b1 - x b) - E b1 b) := hGo b1 b
        have hEsym : E b1 b = (E b b1) := by
          have := hE.isHermitian.apply b b1
          simpa using this
        have hsqrt_mono : Real.sqrt (1 / 4 + 2 * kstar ^ 2) ≤ Real.sqrt (1 / 4 + 2 * (kφ (x b - x b1)) ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
        have hμ1 : μ ≤ 2 * kstar ^ 2 - 2 * a₁ := le_trans (min_le_left _ _) (min_le_left _ _)
        have hμ2 : μ ≤ 4 * kstar ^ 2 - 2 * a₂ := le_trans (min_le_left _ _) (min_le_right _ _)
        have hμ3 : μ ≤ (1 / 2 + Real.sqrt (1 / 4 + 2 * kstar ^ 2)) ^ 2 - 1 - a₁ - a₂ := min_le_right _ _
        simp only [hw, hsb', hs1, if_true, Bool.false_eq_true, if_false]
        rw [hcl]
        rcases hm b with hmb | hmb <;> rcases hm b1 with hmb1 | hmb1
        · -- (1,1)
          obtain ⟨X, hX, htr, h00, h11, h01⟩ := reidx p q hpq (fun y => hu y)
          change X 0 0 = G b b at h00; change X 1 1 = G b1 b1 at h11; change X 0 1 = G b b1 at h01
          rw [htr]
          have hv := block11_ge X hX (δ₁ := (E b b)) (δ₂ := (E b1 b1)) (κ := (kφ (x b - x b1))) (e := (E b b1))
            (by rw [h00, hGd, hmb]; simp) (by rw [h11, hGd, hmb1]; simp)
            (by rw [h01, hGbb1, hmb, hmb1]; simp) (hδ0 b) (hδ0 b1) (hδ1 b) (hδ1 b1) hκ0 hκ1 hee' hpsd
          simp only [hc, hmb, hmb1, if_true]
          linarith
        · -- (1,2)
          obtain ⟨X, hX, htr, h00, h11, h01⟩ := reidx p q hpq (fun y => hu y)
          change X 0 0 = G b b at h00; change X 1 1 = G b1 b1 at h11; change X 0 1 = G b b1 at h01
          rw [htr]
          have hv := block12_ge X hX (δ₁ := (E b b)) (δ₂ := (E b1 b1)) (κ := (kφ (x b - x b1))) (e := (E b b1))
            (by rw [h00, hGd, hmb]; simp) (by rw [h11, hGd, hmb1]; push_cast; ring)
            (by rw [h01, hGbb1, hmb, hmb1]; norm_num) (hδ0 b) (hδ0 b1) hκ0 hee
          have hsq := pow_le_pow_left₀ (by positivity) (add_le_add_left hsqrt_mono (1 / 2)) 2
          simp only [hc, hmb, hmb1, if_true, show (2 : ℕ) ≠ 1 by norm_num, if_false]
          linarith
        · -- (2,1): reindex in the order (b1, b)
          obtain ⟨X, hX, htr, h00, h11, h01⟩ := reidx q p hpq.symm (fun y => (hu y).symm)
          change X 0 0 = G b1 b1 at h00; change X 1 1 = G b b at h11; change X 0 1 = G b1 b at h01
          rw [htr]
          have hv := block12_ge X hX (δ₁ := (E b1 b1)) (δ₂ := (E b b)) (κ := (kφ (x b - x b1))) (e := (E b b1))
            (by rw [h00, hGd, hmb1]; simp) (by rw [h11, hGd, hmb]; push_cast; ring)
            (by rw [h01, hGb1b, hmb, hmb1, ← hκ, hEsym]; norm_num) (hδ0 b1) (hδ0 b) hκ0
            (by rw [mul_comm]; exact hee)
          have hsq := pow_le_pow_left₀ (by positivity) (add_le_add_left hsqrt_mono (1 / 2)) 2
          simp only [hc, hmb, hmb1, if_true, show (2 : ℕ) ≠ 1 by norm_num, if_false]
          linarith
        · -- (2,2)
          obtain ⟨X, hX, htr, h00, h11, h01⟩ := reidx p q hpq (fun y => hu y)
          change X 0 0 = G b b at h00; change X 1 1 = G b1 b1 at h11; change X 0 1 = G b b1 at h01
          rw [htr]
          have hv := block22_ge X hX (δ₁ := (E b b)) (δ₂ := (E b1 b1)) (κ := (kφ (x b - x b1))) (e := (E b b1))
            (by rw [h00, hGd, hmb]; push_cast; ring) (by rw [h11, hGd, hmb1]; push_cast; ring)
            (by rw [h01, hGbb1, hmb, hmb1]; norm_num)
            (hδ0 b) (hδ0 b1) hκ0 hκ1 hee
          simp only [hc, hmb, hmb1, show (2 : ℕ) ≠ 1 by norm_num, if_false]
          linarith
      · -- singleton block {b}
        have hs1' : secB t (b.val + 1) = false := by simpa using hs1
        set p : {i // blk i = b} := ⟨b, (blk_eq_iff t b b).2 (Or.inl ⟨hsb', rfl⟩)⟩
        have hu : (univ : Finset {i // blk i = b}) = {p} := by
          ext ⟨y, hy⟩
          simp only [mem_univ, true_iff, mem_singleton]
          rcases (blk_eq_iff t y b).1 hy with ⟨_, h⟩ | ⟨h1, h⟩
          · exact Subtype.ext h
          · exfalso
            have : y.val = b.val + 1 := h
            rw [this] at h1; rw [h1] at hs1'; simp at hs1'
        simp only [hw, hsb', hs1, Bool.false_eq_true, if_false]
        rw [trFun_single _ p hu, hu, Finset.sum_singleton]
        show -A ≤ fT (G b b) - c b
        rw [hGd]
        have hfT0 := fT_nonneg ((m b : ℝ) * (1 - E b b))
        rcases hm b with hmb | hmb
        · simp only [hc, hmb, if_true, Nat.cast_one, one_mul]
          rw [fT_of_le (by linarith [hδ0 b])]
          have := hδ0 b
          have : a₁ ≤ A := le_max_left _ _
          nlinarith
        · simp only [hc, hmb, show (2 : ℕ) ≠ 1 by norm_num, if_false]
          have : a₂ ≤ A := le_max_right _ _
          have := fT_nonneg (((2 : ℕ) : ℝ) * (1 - E b b))
          linarith
  -- sum of the block values
  have hsum : ∑ b, w b ≤ trFun hG.isHermitian fT - ∑ i, c i := by
    rw [hclaims]
    have := Finset.sum_le_sum fun b (_ : b ∈ univ) => hblock b
    rw [Finset.sum_sub_distrib] at this
    linarith
  -- counting
  set S := univ.filter fun i : Fin n => ∀ j : Fin n, j.val + 1 = i.val → 3 / 4 ≤ x i - x j with hS
  set PL := univ.filter fun b : Fin n => secB t b.val = false ∧ secB t (b.val + 1) = true with hPL
  set SL := univ.filter fun b : Fin n => secB t b.val = false ∧ secB t (b.val + 1) = false with hSL
  have hwsum : ∑ b, w b = μ * #PL - A * #SL := by
    have e1 : ∀ b, w b = μ * (if secB t b.val = false ∧ secB t (b.val + 1) = true then 1 else 0)
        - A * (if secB t b.val = false ∧ secB t (b.val + 1) = false then 1 else 0) := by
      intro b
      simp only [hw]
      cases h1 : secB t b.val <;> cases h2 : secB t (b.val + 1) <;> simp
    simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.natCast_card_filter]
    rfl
  -- starts are pair leaders
  have hSPL : S ⊆ PL := by
    intro i hi
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [hPL, Finset.mem_filter, Finset.mem_univ, true_and]
    have hnot : secB t i.val = false := by
      rcases Nat.eq_zero_or_pos i.val with h0 | hpos
      · rw [h0]; rfl
      · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
        rw [hj, secB_succ]
        have htj : t j = false := by
          by_contra hne
          have htj : t j = true := by simpa using hne
          obtain ⟨hj1, hgap⟩ := (tB_iff x j).1 htj
          have := hi ⟨j, by omega⟩ (by simp; omega)
          have e : (⟨j + 1, hj1⟩ : Fin n) = i := Fin.ext (by simp; omega)
          rw [e] at hgap; linarith
        rw [htj]; rfl
    refine ⟨hnot, ?_⟩
    rw [secB_succ, hnot]
    obtain ⟨j, hj, hjx⟩ := hchain i
    rcases hj with hj | hj
    · have := hi j hj
      have := (abs_lt.1 hjx).2
      linarith
    · have hj1 : i.val + 1 < n := by omega
      have e : (⟨i.val + 1, hj1⟩ : Fin n) = j := Fin.ext (by simp; omega)
      have hlt : i < j := by rw [Fin.lt_def]; omega
      have hxj := hx hlt
      have : x j - x i < 3 / 4 := by rw [abs_sub_comm, abs_of_pos (by linarith)] at hjx; exact hjx
      have htr : t i.val = true := (tB_iff x i.val).2 ⟨hj1, by rw [e]; exact this⟩
      simp [htr]
  have hcardPL : (#S : ℝ) ≤ #PL := by exact_mod_cast Finset.card_le_card hSPL
  -- singleton leaders inject into starts
  have hcardSL : (#SL : ℝ) ≤ #S := by
    have hn : ∀ b : Fin n, 0 < n := fun b => by have := b.isLt; omega
    let g : Fin n → Fin n := fun b => if h : b.val + 1 < n then ⟨b.val + 1, h⟩ else ⟨0, hn b⟩
    have hmaps : ∀ b ∈ SL, g b ∈ S := by
      intro b hb
      simp only [hSL, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj
      by_cases h : b.val + 1 < n
      · have hgb : g b = ⟨b.val + 1, h⟩ := dif_pos h
        rw [hgb] at hj ⊢
        have hjb : j = b := Fin.ext (by simp at hj; omega)
        rw [hjb]
        have htf : t b.val = false := by
          have := hb.2; rw [secB_succ, hb.1] at this; simpa using this
        by_contra hlt
        push_neg at hlt
        have : t b.val = true := (tB_iff x b.val).2 ⟨h, hlt⟩
        rw [htf] at this; exact Bool.false_ne_true this
      · have hgb : g b = ⟨0, hn b⟩ := dif_neg h
        rw [hgb] at hj; simp at hj
    have hinj : Set.InjOn g SL := by
      intro b1 _ b2 _ h
      by_cases h1 : b1.val + 1 < n <;> by_cases h2 : b2.val + 1 < n
      · have := congrArg Fin.val h; simp only [g, dif_pos h1, dif_pos h2] at this; exact Fin.ext (by omega)
      · have := congrArg Fin.val h; simp only [g, dif_pos h1, dif_neg h2] at this; omega
      · have := congrArg Fin.val h; simp only [g, dif_neg h1, dif_pos h2] at this; omega
      · exact Fin.ext (by have := b1.isLt; have := b2.isLt; omega)
    exact_mod_cast Finset.card_le_card_of_injOn g hmaps hinj
  have hnch : (nChains x : ℝ) = #S := rfl
  rw [hTM]
  have hμ0 : 0 ≤ μ := hμ
  rw [hnch]
  have h1 : (#S : ℝ) * μ ≤ μ * #PL := by nlinarith
  have h2 : A * #SL ≤ A * #S := mul_le_mul_of_nonneg_left hcardSL hA0
  have hsum' := hsum
  rw [hwsum] at hsum'
  nlinarith

end ZetaS

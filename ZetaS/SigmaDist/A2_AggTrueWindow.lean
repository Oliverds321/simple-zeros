/-
Node A2 (track K, all-marks) — prop:sigd-agg (sec_zeta.tex l.1139–1162), CORRECTED STATEMENT (L2_2, 28 Sep 2026).

The skeleton statement `agg_true_window` (lean_work/L0_4/skeleton/A2_AggTrueWindow.lean) is FALSE as written: it assumes
neither `C` symmetric nor `kψ` even, and then the pair (i, j), i < j, can have `C i j ≈ kψ(x i − x j) = 0` while only
`C j i ≈ kψ(x j − x i)` is large; the windows count `2 m m′ k²` per pair but `E` only contains `m m′ (C_ij² + C_ji²)`.
Counterexample (exact, `py/a2_counterexample.py`): K = 2, γ₁,₀ = 2, μ₀ = 1, b ≡ 1, k(t) = √(1 − t/2) on [0, 2] and 0
elsewhere, n = 100 sites x_p = 1.5p, m ≡ 1, ε = δ = 0, C_pq = k(x_p − x_q), C_pp = 1: LHS = 71/2 > E = 99/4.

Either missing hypothesis repairs it (both hold in every use: `C = UᵀU`, and `kPsi ψ` is even):
  * `agg_true_window_of_symm` : add `hCsymm : ∀ i j, C i j = C j i`;
  * `agg_true_window_of_even` : add `hkeven : ∀ t, kψ (-t) = kψ t`.
Both follow from `agg_core`, whose pair hypothesis is the two-sided closeness for i < j with the AM bound
`ε + (δ_i + δ_j)/2` (implied by `ε + √(δ_i δ_j)`).

Proof = the draft's (windows of K consecutive sites, capped marks, true-window value F^φ(W) with the symmetrised
entry (C_ij² + C_ji²)/2; upper bound Σ F^φ ≤ E + νΛ; transfer |F^φ − F^ψ| ≤ 8 Σ γ (ε + (δ+δ′)/2); lower bound by
(LI_m); boundary loss ≤ K·Σ_i(|b_i(1)| + |b_i(2)|)). Indices are extended by zero to ℕ.
INTEGRATED (L0_1, 28 Sep 2026): the node's original name `ZetaS.agg_true_window` (end of this file) now carries
the statement of `A2fix.agg_true_window_of_symm` (the skeleton statement plus `hCsymm`), the statement change
accepted by the lead; the skeleton statement (false as written) is withdrawn.
-/
import ZetaS.Interfaces

open Finset

namespace ZetaS

namespace A2fix

/-! ### small helpers -/

lemma tele (f : ℕ → ℝ) (i s : ℕ) : ∑ p ∈ Ico i (i + s), (f (p + 1) - f p) = f (i + s) - f i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), ih]
    ring

lemma filter_image_val {K i s : ℕ} (his : i + s ≤ K - 1) :
    ((univ : Finset (Fin (K - 1))).filter (fun l => i ≤ l.val ∧ l.val < i + s)).image Fin.val
      = Ico i (i + s) := by
  ext p
  simp only [mem_image, mem_filter, mem_univ, true_and, mem_Ico]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact hl
  · intro hp; exact ⟨⟨p, by omega⟩, hp, rfl⟩

lemma gapSpan_tele {K : ℕ} (X : ℕ → ℝ) (t : ℕ) {i s : ℕ} (his : i + s ≤ K - 1) :
    gapSpan (K := K) (fun l : Fin (K - 1) => X (t + l + 1) - X (t + l)) i s = X (t + i + s) - X (t + i) := by
  unfold gapSpan
  have h1 : ∑ l ∈ (univ : Finset (Fin (K - 1))).filter (fun l => i ≤ l.val ∧ l.val < i + s),
      (X (t + l + 1) - X (t + l))
      = ∑ p ∈ ((univ : Finset (Fin (K - 1))).filter (fun l => i ≤ l.val ∧ l.val < i + s)).image Fin.val,
          (X (t + p + 1) - X (t + p)) := by
    rw [Finset.sum_image (fun a _ b _ h => Fin.val_injective h)]
  rw [h1, filter_image_val his]
  have := tele (fun p => X (t + p)) i s
  rw [← Nat.add_assoc] at this
  exact this

lemma sum_shift_le (h : ℕ → ℝ) (hh : ∀ p, 0 ≤ h p) {L i N : ℕ} (hLi : ∀ t < L, t + i < N) :
    ∑ t ∈ range L, h (t + i) ≤ ∑ p ∈ range N, h p := by
  rw [← Finset.sum_image (f := h) (s := range L) (g := fun t => t + i)
    (fun a _ b _ hab => by have : a + i = b + i := hab; omega)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp ⊢
    obtain ⟨t, ht, rfl⟩ := hp
    exact hLi t ht
  · intro p _ _; exact hh p

lemma sq_sub_sq_le {k c e : ℝ} (hk : |k| ≤ 1) (hc : |c| ≤ 1) (h : |c - k| ≤ e) : k ^ 2 - c ^ 2 ≤ 2 * e := by
  have hkc : |k + c| ≤ 2 := by
    rw [abs_le] at hk hc ⊢; constructor <;> linarith
  calc k ^ 2 - c ^ 2 ≤ |(k - c) * (k + c)| := by
        have : k ^ 2 - c ^ 2 = (k - c) * (k + c) := by ring
        rw [this]; exact le_abs_self _
    _ = |c - k| * |k + c| := by rw [abs_mul, abs_sub_comm]
    _ ≤ e * 2 := mul_le_mul h hkc (abs_nonneg _) (le_trans (abs_nonneg _) h)
    _ = 2 * e := by ring

lemma sqrt_le_avg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg (a - b)]

lemma sum_Icc_range_le {K : ℕ} (φ : ℕ → ℕ → ℝ) (hφ : ∀ s i, 0 ≤ φ s i) :
    ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), φ s i ≤ ∑ s ∈ range K, ∑ i ∈ range K, φ s i := by
  calc ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), φ s i
      ≤ ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range K, φ s i := by
        apply Finset.sum_le_sum; intro s _
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi; simp only [mem_range] at hi ⊢; omega
        · intro i _ _; exact hφ s i
    _ ≤ ∑ s ∈ range K, ∑ i ∈ range K, φ s i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro s hs; simp only [mem_Icc, mem_range] at hs ⊢; omega
        · intro s _ _; exact Finset.sum_nonneg fun i _ => hφ s i

/-! ### the core statement -/

theorem agg_core {K : ℕ} (W : MarkWeights K) (kψ : ℝ → ℝ) (hcert : LocalCertAM kψ W)
    (hk1 : ∀ t, |kψ t| ≤ 1)
    {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ i j, x j - x i ≤ Λ)
    (m : Fin n → ℕ) (hm : ∀ i, 1 ≤ m i)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC1 : ∀ i j, |C i j| ≤ 1)
    (δ : Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i) {ε : ℝ} (hε : 0 ≤ ε)
    (hpair : ∀ i j : Fin n, i < j →
      |C i j - kψ (x j - x i)| ≤ ε + (δ i + δ j) / 2 ∧ |C j i - kψ (x j - x i)| ≤ ε + (δ i + δ j) / 2) :
    W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ)
        - W.nu * Λ - 16 * (K : ℝ) ^ 2 * (ε * n + ∑ i, δ i)
        - 2 * K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)
      ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * (C i j) ^ 2 := by
  classical
  have hK2 : 2 ≤ K := W.two_le
  -- extensions by zero
  let xe : ℕ → ℝ := fun p => if h : p < n then x ⟨p, h⟩ else 0
  let Ce : ℕ → ℕ → ℝ := fun p q => if h : p < n ∧ q < n then C ⟨p, h.1⟩ ⟨q, h.2⟩ else 0
  let δe : ℕ → ℝ := fun p => if h : p < n then δ ⟨p, h⟩ else 0
  let me : ℕ → ℝ := fun p => if h : p < n then (m ⟨p, h⟩ : ℝ) else 0
  let mk : ℕ → Fin 2 := fun p => if h : p < n then (if m ⟨p, h⟩ = 1 then 0 else 1) else 0
  let mv : ℕ → ℝ := fun p => ((mk p : ℕ) : ℝ) + 1
  have hδe : ∀ p, 0 ≤ δe p := by
    intro p; simp only [δe]; split_ifs with h
    · exact hδ _
    · exact le_rfl
  have hmv0 : ∀ p, 0 ≤ mv p := fun p => by simp only [mv]; positivity
  have hmv_le : ∀ p (h : p < n), mv p ≤ me p := by
    intro p h
    simp only [mv, mk, me, dif_pos h]
    have := hm ⟨p, h⟩
    split_ifs with h1
    · simp [h1]
    · have : 2 ≤ m ⟨p, h⟩ := by omega
      have : (2 : ℝ) ≤ (m ⟨p, h⟩ : ℝ) := by exact_mod_cast this
      simp only [Fin.isValue, Fin.val_one, Nat.cast_one]; linarith
  have hmv_le2 : ∀ p, mv p ≤ 2 := by
    intro p; simp only [mv]
    have := (mk p).isLt
    have : ((mk p : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : (mk p : ℕ) ≤ 1)
    linarith
  -- windows
  set Lw : ℕ := n + 1 - K with hLw
  have hwin : ∀ t < Lw, ∀ i < K, t + i < n := by intro t ht i hi; omega
  let mw : ℕ → Fin K → Fin 2 := fun t i => mk (t + i)
  let gw : ℕ → Fin (K - 1) → ℝ := fun t l => xe (t + l + 1) - xe (t + l)
  let Aφ : ℕ → ℕ → ℝ := fun p q => (Ce p q ^ 2 + Ce q p ^ 2) / 2
  let Pφ : ℕ → ℝ := fun t => ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
      W.γ s i * (mv (t + i) * mv (t + i + s) * Aφ (t + i) (t + i + s))
  let err : ℕ → ℝ := fun t => ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
      W.γ s i * (8 * (ε + (δe (t + i) + δe (t + i + s)) / 2))
  let Gp : ℕ → ℝ := fun t => ∑ l, W.μ l * gw t l
  -- (F1) marks of a window
  have hF1 : ∀ t j, j < K → markVal (mw t) j = mv (t + j) := by
    intro t j hj
    simp only [markVal, dif_pos hj, mw, mv]
  -- (F4) one window
  have hF4 : ∀ t < Lw, ∑ i, W.b i (mw t i) ≤ Pφ t + err t + Gp t := by
    intro t ht
    have hg : ∀ l, 0 ≤ gw t l := by
      intro l
      have hl := l.isLt
      have h1 : t + l + 1 < n := by omega
      have h2 : t + l < n := by omega
      simp only [gw, xe, dif_pos h1, dif_pos h2, sub_nonneg]
      exact (hx (Fin.mk_lt_mk.2 (by omega))).le
    refine (hcert (mw t) (gw t) hg).trans ?_
    unfold localFm
    have hpairs : ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
        W.γ s i * markVal (mw t) i * markVal (mw t) (i + s) * kψ (gapSpan (gw t) i s) ^ 2
        ≤ Pφ t + err t := by
      simp only [Pφ, err, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      have hs' := Finset.mem_Icc.1 hs
      have hi' := Finset.mem_range.1 hi
      have his : i + s ≤ K - 1 := by omega
      rw [hF1 t i (by omega), hF1 t (i + s) (by omega), gapSpan_tele xe t his, ← Nat.add_assoc]
      have hp : t + i < n := by omega
      have hq : t + i + s < n := by omega
      have hγ : 0 ≤ W.γ s i := W.γ_nonneg s hs i hi
      -- the entries
      obtain ⟨h1, h2⟩ := hpair ⟨t + i, hp⟩ ⟨t + i + s, hq⟩ (Fin.mk_lt_mk.2 (by omega))
      have hxq : xe (t + i + s) = x ⟨t + i + s, hq⟩ := dif_pos hq
      have hxp : xe (t + i) = x ⟨t + i, hp⟩ := dif_pos hp
      have hCpq : Ce (t + i) (t + i + s) = C ⟨t + i, hp⟩ ⟨t + i + s, hq⟩ := dif_pos ⟨hp, hq⟩
      have hCqp : Ce (t + i + s) (t + i) = C ⟨t + i + s, hq⟩ ⟨t + i, hp⟩ := dif_pos ⟨hq, hp⟩
      have hδp : δe (t + i) = δ ⟨t + i, hp⟩ := dif_pos hp
      have hδq : δe (t + i + s) = δ ⟨t + i + s, hq⟩ := dif_pos hq
      set e := ε + (δ ⟨t + i, hp⟩ + δ ⟨t + i + s, hq⟩) / 2 with he
      have he0 : 0 ≤ e := by have := hδ ⟨t + i, hp⟩; have := hδ ⟨t + i + s, hq⟩; positivity
      have k1 := hk1 (x ⟨t + i + s, hq⟩ - x ⟨t + i, hp⟩)
      have d1 := sq_sub_sq_le k1 (hC1 _ _) h1
      have d2 := sq_sub_sq_le k1 (hC1 _ _) h2
      have hA : kψ (x ⟨t + i + s, hq⟩ - x ⟨t + i, hp⟩) ^ 2 - Aφ (t + i) (t + i + s) ≤ 2 * e := by
        simp only [Aφ, hCpq, hCqp]; linarith
      have hmm0 : 0 ≤ mv (t + i) * mv (t + i + s) := mul_nonneg (hmv0 _) (hmv0 _)
      have hmm4 : mv (t + i) * mv (t + i + s) ≤ 4 := by
        have := hmv_le2 (t + i); have := hmv_le2 (t + i + s)
        nlinarith [hmv0 (t + i), hmv0 (t + i + s)]
      rw [hxq, hxp, hδp, hδq, ← he]
      have key : mv (t + i) * mv (t + i + s) * kψ (x ⟨t + i + s, hq⟩ - x ⟨t + i, hp⟩) ^ 2
          ≤ mv (t + i) * mv (t + i + s) * Aφ (t + i) (t + i + s) + 8 * e := by
        have : mv (t + i) * mv (t + i + s) * (kψ (x ⟨t + i + s, hq⟩ - x ⟨t + i, hp⟩) ^ 2
            - Aφ (t + i) (t + i + s)) ≤ 4 * (2 * e) := by
          calc _ ≤ mv (t + i) * mv (t + i + s) * (2 * e) := mul_le_mul_of_nonneg_left hA hmm0
            _ ≤ 4 * (2 * e) := mul_le_mul_of_nonneg_right hmm4 (by positivity)
        nlinarith
      calc W.γ s i * mv (t + i) * mv (t + i + s) * kψ (x ⟨t + i + s, hq⟩ - x ⟨t + i, hp⟩) ^ 2
          = W.γ s i * (mv (t + i) * mv (t + i + s) * kψ (x ⟨t + i + s, hq⟩ - x ⟨t + i, hp⟩) ^ 2) := by ring
        _ ≤ W.γ s i * (mv (t + i) * mv (t + i + s) * Aφ (t + i) (t + i + s) + 8 * e) :=
            mul_le_mul_of_nonneg_left key hγ
        _ = _ := by ring
    have : Gp t = ∑ l, W.μ l * gw t l := rfl
    linarith
  -- (F5) the pair parts add up to at most E
  let f : ℕ → ℕ → ℝ := fun p q => me p * me q * Ce p q ^ 2
  have hf0 : ∀ p q, 0 ≤ f p q := by
    intro p q; simp only [f, me]
    split_ifs <;> positivity
  have hE : (∑ i, ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * (C i j) ^ 2)
      = ∑ q ∈ ((range n) ×ˢ (range n)).filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
    rw [Finset.sum_filter, Finset.sum_product, Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_range.1 hp
    rw [dif_pos hp', Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := Finset.mem_range.1 hq
    rw [dif_pos hq']
    simp only [f, me, Ce, dif_pos hp', dif_pos hq', dif_pos (And.intro hp' hq'), Fin.mk.injEq]
    split_ifs <;> simp_all
  have hF5 : ∑ t ∈ range Lw, Pφ t ≤ ∑ q ∈ ((range n) ×ˢ (range n)).filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
    let w : ℕ → ℕ → ℝ := fun s p => mv p * mv (p + s) * Aφ p (p + s)
    have hw0 : ∀ s p, 0 ≤ w s p := by
      intro s p; simp only [w, Aφ]
      have := hmv0 p; have := hmv0 (p + s); positivity
    -- swap and shift
    have step1 : ∑ t ∈ range Lw, Pφ t
        = ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i) := by
      simp only [Pφ, w]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    have step2 : ∀ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i)
        ≤ 2 * ∑ p ∈ range (n - s), w s p := by
      intro s hs
      have hs' := Finset.mem_Icc.1 hs
      calc ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i)
          ≤ ∑ i ∈ range (K - s), W.γ s i * ∑ p ∈ range (n - s), w s p := by
            apply Finset.sum_le_sum; intro i hi
            have hi' := Finset.mem_range.1 hi
            apply mul_le_mul_of_nonneg_left _ (W.γ_nonneg s hs i hi)
            exact sum_shift_le (w s) (hw0 s) (fun t ht => by omega)
        _ = 2 * ∑ p ∈ range (n - s), w s p := by rw [← Finset.sum_mul, W.γ_sum s hs]
    have step3 : ∀ s ∈ Icc 1 (K - 1), 2 * ∑ p ∈ range (n - s), w s p
        ≤ ∑ p ∈ range (n - s), (f p (p + s) + f (p + s) p) := by
      intro s hs
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro p hp
      have hp' := Finset.mem_range.1 hp
      have h1 : p < n := by omega
      have h2 : p + s < n := by omega
      simp only [w, f, Aφ]
      have a1 := hmv_le p h1; have a2 := hmv_le (p + s) h2
      have b1 := hmv0 p; have b2 := hmv0 (p + s)
      have c1 := sq_nonneg (Ce p (p + s)); have c2 := sq_nonneg (Ce (p + s) p)
      have : mv p * mv (p + s) ≤ me p * me (p + s) := mul_le_mul a1 a2 b2 (b1.trans a1)
      have : 0 ≤ mv p * mv (p + s) := mul_nonneg b1 b2
      nlinarith
    have step4 : ∑ s ∈ Icc 1 (K - 1), ∑ p ∈ range (n - s), (f p (p + s) + f (p + s) p)
        ≤ ∑ q ∈ ((range n) ×ˢ (range n)).filter (fun q => q.1 ≠ q.2), f q.1 q.2 := by
      rw [Finset.sum_sigma']
      set S := (Icc 1 (K - 1)).sigma (fun s => range (n - s)) with hS
      let φ1 : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun y => (y.2, y.2 + y.1)
      let φ2 : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun y => (y.2 + y.1, y.2)
      have hmemS : ∀ y ∈ S, 1 ≤ y.1 ∧ y.2 + y.1 < n := by
        intro y hy
        rw [hS, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_range] at hy
        omega
      have inj1 : ∀ a ∈ S, ∀ b ∈ S, φ1 a = φ1 b → a = b := by
        rintro ⟨s, p⟩ _ ⟨s', p'⟩ _ h
        simp only [φ1, Prod.mk.injEq] at h
        obtain ⟨rfl, h2⟩ := h
        have : s = s' := by omega
        subst this; rfl
      have inj2 : ∀ a ∈ S, ∀ b ∈ S, φ2 a = φ2 b → a = b := by
        rintro ⟨s, p⟩ _ ⟨s', p'⟩ _ h
        simp only [φ2, Prod.mk.injEq] at h
        obtain ⟨h1, rfl⟩ := h
        have : s = s' := by omega
        subst this; rfl
      have hdisj : Disjoint (S.image φ1) (S.image φ2) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_image] at ha hb
        obtain ⟨y, hy, rfl⟩ := ha
        obtain ⟨z, hz, hyz⟩ := hb
        have := hmemS y hy; have := hmemS z hz
        simp only [φ1, φ2, Prod.mk.injEq] at hyz
        omega
      have hsub : S.image φ1 ∪ S.image φ2 ⊆ ((range n) ×ˢ (range n)).filter (fun q => q.1 ≠ q.2) := by
        intro a ha
        rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ha
        rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
        rcases ha with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
        · have := hmemS y hy; simp only [φ1]; omega
        · have := hmemS y hy; simp only [φ2]; omega
      calc ∑ y ∈ S, (f y.2 (y.2 + y.1) + f (y.2 + y.1) y.2)
          = ∑ q ∈ S.image φ1, f q.1 q.2 + ∑ q ∈ S.image φ2, f q.1 q.2 := by
            rw [Finset.sum_image inj1, Finset.sum_image inj2, ← Finset.sum_add_distrib]
        _ = ∑ q ∈ S.image φ1 ∪ S.image φ2, f q.1 q.2 := (Finset.sum_union hdisj).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => hf0 q.1 q.2)
    calc ∑ t ∈ range Lw, Pφ t
        = ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), W.γ s i * ∑ t ∈ range Lw, w s (t + i) := step1
      _ ≤ ∑ s ∈ Icc 1 (K - 1), 2 * ∑ p ∈ range (n - s), w s p := Finset.sum_le_sum step2
      _ ≤ ∑ s ∈ Icc 1 (K - 1), ∑ p ∈ range (n - s), (f p (p + s) + f (p + s) p) :=
          Finset.sum_le_sum step3
      _ ≤ _ := step4
  -- (F6) the gap parts
  have hF6 : ∑ t ∈ range Lw, Gp t ≤ W.nu * Λ := by
    simp only [Gp]
    rw [Finset.sum_comm]
    have hin : ∀ l : Fin (K - 1), ∑ t ∈ range Lw, W.μ l * gw t l ≤ W.μ l * Λ := by
      intro l
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (W.μ_nonneg l)
      have htel : ∑ t ∈ range Lw, gw t l = xe (Lw + l) - xe (0 + l) := by
        rw [← Finset.sum_range_sub (fun t => xe (t + l)) Lw]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [gw]
        rw [Nat.add_right_comm t 1 (l : ℕ)]
      rw [htel]
      rcases Nat.eq_zero_or_pos Lw with h0 | hpos
      · rw [h0]; simp [hΛ0]
      · have hl := l.isLt
        have h1 : Lw + l < n := by omega
        have h2 : 0 + (l : ℕ) < n := by omega
        simp only [xe, dif_pos h1, dif_pos h2]
        exact hΛ _ _
    calc ∑ l, ∑ t ∈ range Lw, W.μ l * gw t l ≤ ∑ l, W.μ l * Λ := Finset.sum_le_sum fun l _ => hin l
      _ = W.nu * Λ := by rw [← Finset.sum_mul]; rfl
  -- (F7) the transfer errors
  have hΔ : ∑ p ∈ range n, δe p = ∑ i, δ i := by
    rw [Finset.sum_fin_eq_sum_range]
  have hF7 : ∑ t ∈ range Lw, err t ≤ 16 * (K : ℝ) ^ 2 * (ε * n + ∑ i, δ i) := by
    set Δ := ∑ i, δ i with hΔdef
    have hγ2 : ∀ s ∈ Icc 1 (K - 1), ∀ i ∈ range (K - s), W.γ s i ≤ 2 := by
      intro s hs i hi
      rw [← W.γ_sum s hs]
      exact Finset.single_le_sum (fun j hj => W.γ_nonneg s hs j hj) hi
    have hLwn : (Lw : ℝ) ≤ n := by exact_mod_cast (by omega : Lw ≤ n)
    have e1 : ∀ t ∈ range Lw, err t ≤ ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
        (16 * ε + 8 * δe (t + i) + 8 * δe (t + i + s)) := by
      intro t _
      apply Finset.sum_le_sum; intro s hs
      apply Finset.sum_le_sum; intro i hi
      have := hγ2 s hs i hi
      have := W.γ_nonneg s hs i hi
      have := hδe (t + i); have := hδe (t + i + s)
      have h8 : 0 ≤ 8 * (ε + (δe (t + i) + δe (t + i + s)) / 2) := by positivity
      nlinarith
    calc ∑ t ∈ range Lw, err t
        ≤ ∑ t ∈ range Lw, ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s),
            (16 * ε + 8 * δe (t + i) + 8 * δe (t + i + s)) := Finset.sum_le_sum e1
      _ = ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), ∑ t ∈ range Lw,
            (16 * ε + 8 * δe (t + i) + 8 * δe (t + i + s)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_comm]
      _ ≤ ∑ s ∈ Icc 1 (K - 1), ∑ i ∈ range (K - s), (16 * (ε * n + Δ)) := by
          apply Finset.sum_le_sum; intro s hs
          apply Finset.sum_le_sum; intro i hi
          have hs' := Finset.mem_Icc.1 hs
          have hi' := Finset.mem_range.1 hi
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, card_range,
            nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
          have s1 : ∑ t ∈ range Lw, δe (t + i) ≤ Δ := by
            rw [← hΔ]; exact sum_shift_le δe hδe (fun t ht => by omega)
          have s2 : ∑ t ∈ range Lw, δe (t + i + s) ≤ Δ := by
            have : ∑ t ∈ range Lw, δe (t + i + s) = ∑ t ∈ range Lw, δe (t + (i + s)) := by
              refine Finset.sum_congr rfl fun t _ => ?_; rw [Nat.add_assoc]
            rw [this, ← hΔ]; exact sum_shift_le δe hδe (fun t ht => by omega)
          have : (Lw : ℝ) * (16 * ε) ≤ n * (16 * ε) := mul_le_mul_of_nonneg_right hLwn (by positivity)
          nlinarith
      _ ≤ ∑ s ∈ range K, ∑ i ∈ range K, (16 * (ε * n + Δ)) := by
          apply sum_Icc_range_le (fun _ _ => 16 * (ε * n + Δ))
          intro _ _
          have : 0 ≤ Δ := Finset.sum_nonneg fun i _ => hδ i
          positivity
      _ = 16 * (K : ℝ) ^ 2 * (ε * n + Δ) := by
          simp only [Finset.sum_const, card_range, nsmul_eq_mul]; ring
  -- (F8) the claims
  have hF8 : W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ)
      - K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|) ≤ ∑ t ∈ range Lw, ∑ i, W.b i (mw t i) := by
    -- the full sum over sites
    have hfull : ∑ i : Fin K, ∑ p ∈ range n, W.b i (mk p)
        = W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ) := by
      rw [Finset.sum_comm]
      have : ∀ p ∈ range n, ∑ i : Fin K, W.b i (mk p) = W.a (mk p) := fun p _ => rfl
      rw [Finset.sum_congr rfl this, ← Fin.sum_univ_eq_sum_range (fun p => W.a (mk p)) n]
      rw [Finset.natCast_card_filter, Finset.natCast_card_filter, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj := j.isLt
      simp only [mk, dif_pos hj]
      have := hm j
      by_cases h1 : m j = 1
      · simp [h1]
      · have h2 : 2 ≤ m j := by omega
        simp [h1, h2]
    -- each position loses at most K sites
    have hpos : ∀ i : Fin K, ∑ p ∈ range n, W.b i (mk p) - K * (|W.b i 0| + |W.b i 1|)
        ≤ ∑ t ∈ range Lw, W.b i (mk (t + i)) := by
      intro i
      set S := (range Lw).image (fun t => t + (i : ℕ)) with hS
      have hinj : ∀ a ∈ range Lw, ∀ b ∈ range Lw, a + (i : ℕ) = b + i → a = b := by
        intro a _ b _ h; omega
      have hSsub : S ⊆ range n := by
        intro p hp
        rw [hS, Finset.mem_image] at hp
        obtain ⟨t, ht, rfl⟩ := hp
        rw [Finset.mem_range] at ht ⊢
        have := i.isLt
        omega
      have hsumS : ∑ p ∈ S, W.b i (mk p) = ∑ t ∈ range Lw, W.b i (mk (t + i)) := by
        rw [hS, Finset.sum_image hinj]
      have hcardS : #S = Lw := by rw [hS, Finset.card_image_of_injOn hinj, card_range]
      have hcard : #(range n \ S) ≤ K := by
        rw [Finset.card_sdiff_of_subset hSsub, hcardS, card_range]; omega
      have hup : ∀ p ∈ range n \ S, W.b i (mk p) ≤ |W.b i 0| + |W.b i 1| := by
        intro p _
        have h0 := le_abs_self (W.b i 0); have h1 := le_abs_self (W.b i 1)
        have ha0 := abs_nonneg (W.b i 0); have ha1 := abs_nonneg (W.b i 1)
        rcases Fin.exists_fin_two.1 ⟨mk p, rfl⟩ with h | h <;> rw [h] <;> linarith
      have hrest : ∑ p ∈ range n \ S, W.b i (mk p) ≤ (K : ℝ) * (|W.b i 0| + |W.b i 1|) := by
        have := Finset.sum_le_card_nsmul (range n \ S) (fun p => W.b i (mk p)) _ hup
        rw [nsmul_eq_mul] at this
        have hc : (#(range n \ S) : ℝ) ≤ K := by exact_mod_cast hcard
        have hB : 0 ≤ |W.b i 0| + |W.b i 1| := by positivity
        nlinarith
      rw [← Finset.sum_sdiff hSsub, hsumS]
      linarith
    calc W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ)
          - K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)
        = ∑ i : Fin K, (∑ p ∈ range n, W.b i (mk p) - K * (|W.b i 0| + |W.b i 1|)) := by
          rw [Finset.sum_sub_distrib, hfull, ← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ ∑ i : Fin K, ∑ t ∈ range Lw, W.b i (mk (t + i)) := Finset.sum_le_sum fun i _ => hpos i
      _ = ∑ t ∈ range Lw, ∑ i, W.b i (mw t i) := by rw [Finset.sum_comm]
  -- assembly
  have hsum4 : ∑ t ∈ range Lw, ∑ i, W.b i (mw t i)
      ≤ ∑ t ∈ range Lw, Pφ t + ∑ t ∈ range Lw, err t + ∑ t ∈ range Lw, Gp t := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun t ht => hF4 t (Finset.mem_range.1 ht)
  have hB : 0 ≤ (∑ i, |W.b i 0|) + ∑ i, |W.b i 1| := by positivity
  have hKB : (K : ℝ) * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|) ≤ 2 * K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|) := by
    have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  rw [hE]
  linarith

/-! ### the two corrected forms of `agg_true_window` -/

/-- **A2, corrected (a)**: the skeleton statement plus `C` symmetric (true for `C = UᵀU`). -/
theorem agg_true_window_of_symm {K : ℕ} (W : MarkWeights K) (kψ : ℝ → ℝ) (hcert : LocalCertAM kψ W)
    (hk1 : ∀ t, |kψ t| ≤ 1)
    {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ i j, x j - x i ≤ Λ)
    (m : Fin n → ℕ) (hm : ∀ i, 1 ≤ m i)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC1 : ∀ i j, |C i j| ≤ 1) (hCsymm : ∀ i j, C i j = C j i)
    (δ : Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i) {ε : ℝ} (hε : 0 ≤ ε)
    (hCk : ∀ i j, i ≠ j → |C i j - kψ (x i - x j)| ≤ ε + Real.sqrt (δ i * δ j)) :
    W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ)
        - W.nu * Λ - 16 * (K : ℝ) ^ 2 * (ε * n + ∑ i, δ i)
        - 2 * K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)
      ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * (C i j) ^ 2 := by
  refine agg_core W kψ hcert hk1 x hx hΛ0 hΛ m hm C hC1 δ hδ hε ?_
  intro i j hij
  have h := hCk j i (ne_of_gt hij)
  have hs : Real.sqrt (δ j * δ i) ≤ (δ i + δ j) / 2 := by
    rw [mul_comm]; exact sqrt_le_avg (hδ i) (hδ j)
  have h' : |C j i - kψ (x j - x i)| ≤ ε + (δ i + δ j) / 2 := by linarith
  exact ⟨by rw [hCsymm]; exact h', h'⟩

/-- **A2, corrected (b)**: the skeleton statement plus `kψ` even (true for `kPsi ψ`). -/
theorem agg_true_window_of_even {K : ℕ} (W : MarkWeights K) (kψ : ℝ → ℝ) (hcert : LocalCertAM kψ W)
    (hk1 : ∀ t, |kψ t| ≤ 1) (hkeven : ∀ t, kψ (-t) = kψ t)
    {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ i j, x j - x i ≤ Λ)
    (m : Fin n → ℕ) (hm : ∀ i, 1 ≤ m i)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC1 : ∀ i j, |C i j| ≤ 1)
    (δ : Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i) {ε : ℝ} (hε : 0 ≤ ε)
    (hCk : ∀ i j, i ≠ j → |C i j - kψ (x i - x j)| ≤ ε + Real.sqrt (δ i * δ j)) :
    W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ)
        - W.nu * Λ - 16 * (K : ℝ) ^ 2 * (ε * n + ∑ i, δ i)
        - 2 * K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)
      ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * (C i j) ^ 2 := by
  refine agg_core W kψ hcert hk1 x hx hΛ0 hΛ m hm C hC1 δ hδ hε ?_
  intro i j hij
  have h1 := hCk i j (ne_of_lt hij)
  have h2 := hCk j i (ne_of_gt hij)
  have hs1 : Real.sqrt (δ i * δ j) ≤ (δ i + δ j) / 2 := sqrt_le_avg (hδ i) (hδ j)
  have hs2 : Real.sqrt (δ j * δ i) ≤ (δ i + δ j) / 2 := by
    rw [mul_comm]; exact sqrt_le_avg (hδ i) (hδ j)
  have hev : kψ (x i - x j) = kψ (x j - x i) := by
    rw [← hkeven (x j - x i), neg_sub]
  rw [hev] at h1
  exact ⟨by linarith, by linarith⟩

end A2fix

end ZetaS

namespace ZetaS

open Finset

/-- **Node A2** (prop:sigd-agg) under the node's original name, with the statement change ACCEPTED by the lead
(28 Sep 2026): the skeleton statement plus `hCsymm : ∀ i j, C i j = C j i` — the statement of
`A2fix.agg_true_window_of_symm` (L2_2). -/
theorem agg_true_window {K : ℕ} (W : MarkWeights K) (kψ : ℝ → ℝ) (hcert : LocalCertAM kψ W)
    (hk1 : ∀ t, |kψ t| ≤ 1)
    {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ i j, x j - x i ≤ Λ)
    (m : Fin n → ℕ) (hm : ∀ i, 1 ≤ m i)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC1 : ∀ i j, |C i j| ≤ 1) (hCsymm : ∀ i j, C i j = C j i)
    (δ : Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i) {ε : ℝ} (hε : 0 ≤ ε)
    (hCk : ∀ i j, i ≠ j → |C i j - kψ (x i - x j)| ≤ ε + Real.sqrt (δ i * δ j)) :
    W.a 0 * (#(univ.filter fun i => m i = 1) : ℝ) + W.a 1 * (#(univ.filter fun i => 2 ≤ m i) : ℝ)
        - W.nu * Λ - 16 * (K : ℝ) ^ 2 * (ε * n + ∑ i, δ i)
        - 2 * K * ((∑ i, |W.b i 0|) + ∑ i, |W.b i 1|)
      ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else (m i : ℝ) * m j * (C i j) ^ 2 :=
  A2fix.agg_true_window_of_symm W kψ hcert hk1 x hx hΛ0 hΛ m hm C hC1 hCsymm δ hδ hε hCk

end ZetaS

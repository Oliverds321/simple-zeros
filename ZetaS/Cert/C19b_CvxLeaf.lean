/-
lean_work/L5_1/C19b_CvxLeaf_proof.lean — track C node C19b (L1_1b statement, byte-identical), L5_1, 28 Sep 2026.
Proof of `checkConvex_sound` against: C13 `spanBounds_sound` (skeleton, L5_2), C09 `KPt.sound`, C08 derivatives,
C14 `taylor2_minorant`, and the CORRECTED C19a `psdLDL_sound_symm` (symmetry discharged here).
Invariant of the fold over the spans (v = g − ĝ):  Flo + Σ_l G_l v_l + ½ vᵀPv ≤ Σ_{processed} γ′ w(x_t) + μ·g,
with G_l ∈ grad_l.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C08_KCosDerivs
import ZetaS.Cert.C09_KEncl
import ZetaS.Cert.C13_SpanBounds
import ZetaS.Cert.C14_Taylor2Minorant
import ZetaS.Cert.C19a_PsdLDL

noncomputable section

open Set

namespace ZetaS.CertV2

private lemma lrs {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

private lemma getD_range_map {α : Type*} (f : ℕ → α) {n l : ℕ} (d0 : α) (hl : l < n) :
    ((List.range n).map f).getD l d0 = f l := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]; simp

private lemma center_getD (B : Box) (l : ℕ) :
    B.center.getD l 0 = ((B.getD l (0, 0)).1 + (B.getD l (0, 0)).2) / 2 := by
  unfold Box.center
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases B[l]? <;> simp

private lemma half_getD (B : Box) (l : ℕ) :
    B.half.getD l 0 = ((B.getD l (0, 0)).2 - (B.getD l (0, 0)).1) / 2 := by
  unfold Box.half
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases B[l]? <;> simp

private lemma lsum_cast (v : List ℚ) (i s : ℕ) :
    ((lsum v i s : ℚ) : ℝ) = ∑ t ∈ Finset.range s, ((v.getD (i + t) 0 : ℚ) : ℝ) := by
  unfold lsum; rw [lrs]; push_cast; rfl

private def vv (gh : List ℚ) (g : ℕ → ℝ) (l : ℕ) : ℝ := g l - ((gh.getD l 0 : ℚ) : ℝ)

private def qf (P : List (List ℚ)) (n : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, (((P.getD a []).getD b 0 : ℚ) : ℝ) * v a * v b

private lemma span_sum (n i s : ℕ) (hs : i + s ≤ n) (v : ℕ → ℝ) :
    ∑ l ∈ Finset.range n, (if i ≤ l ∧ l < i + s then v l else 0) = ∑ t ∈ Finset.range s, v (i + t) := by
  rw [← Finset.sum_filter]
  have : (Finset.range n).filter (fun l => i ≤ l ∧ l < i + s) = Finset.Ico i (i + s) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Finset.sum_Ico_eq_sum_range]; simp

private lemma qf_update (P P' : List (List ℚ)) (n i s : ℕ) (v : ℕ → ℝ) (c : ℚ)
    (hP' : ∀ a < n, ∀ b < n, (P'.getD a []).getD b 0 =
      (P.getD a []).getD b 0 + (if (i ≤ a ∧ a < i + s) ∧ (i ≤ b ∧ b < i + s) then c else 0)) :
    qf P' n v = qf P n v + (c : ℝ) * (∑ a ∈ Finset.range n, if i ≤ a ∧ a < i + s then v a else 0) ^ 2 := by
  unfold qf
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [hP' a (Finset.mem_range.mp ha) b (Finset.mem_range.mp hb)]
  by_cases ha' : i ≤ a ∧ a < i + s <;> by_cases hb' : i ≤ b ∧ b < i + s <;> simp [ha', hb'] <;> ring

private lemma gradsum_update (G : ℕ → ℝ) (n i s : ℕ) (v : ℕ → ℝ) (e : ℝ) :
    ∑ l ∈ Finset.range n, (G l + (if i ≤ l ∧ l < i + s then e else 0)) * v l =
      ∑ l ∈ Finset.range n, G l * v l + e * ∑ l ∈ Finset.range n, (if i ≤ l ∧ l < i + s then v l else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> ring

/-- the fold invariant. -/
private def Inv (D : LIQ) (gh : List ℚ) (g : ℕ → ℝ) (acc : CAcc) (Fp : ℝ) : Prop :=
  acc.grad.length = D.d ∧ acc.P.length = D.d ∧ (∀ a < D.d, (acc.P.getD a []).length = D.d) ∧
  (∀ a < D.d, ∀ b < D.d, (acc.P.getD a []).getD b 0 = (acc.P.getD b []).getD a 0) ∧
  ∃ G : ℕ → ℝ, (∀ l < D.d, (acc.grad.getD l (QI.pt 0)).Contains (G l)) ∧
    ((acc.Flo : ℚ) : ℝ) + ∑ l ∈ Finset.range D.d, G l * vv gh g l + qf acc.P D.d (vv gh g) / 2 ≤ Fp

private lemma step {D : LIQ} {B : Box} {gh : List ℚ} {g : ℕ → ℝ} (hg : B.Mem D.d g)
    (hin : ∀ l < D.d, (B.getD l (0, 0)).1 ≤ gh.getD l 0 ∧ gh.getD l 0 ≤ (B.getD l (0, 0)).2)
    (i s : ℕ) (γ : ℚ) (hγ : 0 ≤ γ) (hsd : i + s ≤ D.d) (sd : SpanD) (acc : CAcc) (Fp : ℝ)
    (hI : Inv D gh g acc Fp) (hok : (cvxSpan B.center B.half gh acc (i, s, γ) sd).ok = true) :
    Inv D gh g (cvxSpan B.center B.half gh acc (i, s, γ) sd) (Fp + (γ : ℝ) * wK (spanVal g i s)) := by
  obtain ⟨hgl, hPl, hrows, hsym, G, hG, hineq⟩ := hI
  have hok' := hok
  simp only [cvxSpan, Bool.and_eq_true, decide_eq_true_eq] at hok'
  obtain ⟨⟨-, hsb⟩, hhx⟩ := hok'
  -- the span interval contains x and x̂
  have hlo : ∀ t < s, (((B.getD (i + t) (0, 0)).1 : ℚ) : ℝ) ≤ g (i + t) := fun t ht => (hg (i + t) (by omega)).1
  have hhi : ∀ t < s, g (i + t) ≤ (((B.getD (i + t) (0, 0)).2 : ℚ) : ℝ) := fun t ht => (hg (i + t) (by omega)).2
  have hcr : ∀ l, (((B.center.getD l 0 : ℚ)) : ℝ) - ((B.half.getD l 0 : ℚ) : ℝ) = (((B.getD l (0, 0)).1 : ℚ) : ℝ) ∧
      (((B.center.getD l 0 : ℚ)) : ℝ) + ((B.half.getD l 0 : ℚ) : ℝ) = (((B.getD l (0, 0)).2 : ℚ) : ℝ) := by
    intro l; rw [center_getD, half_getD]; push_cast; constructor <;> ring
  have hx1 : ((lsum B.center i s : ℚ) : ℝ) - ((lsum B.half i s : ℚ) : ℝ) ≤ spanVal g i s := by
    rw [lsum_cast, lsum_cast, ← Finset.sum_sub_distrib]; unfold spanVal
    exact Finset.sum_le_sum fun t ht => by rw [(hcr _).1]; exact hlo t (Finset.mem_range.mp ht)
  have hx2 : spanVal g i s ≤ ((lsum B.center i s : ℚ) : ℝ) + ((lsum B.half i s : ℚ) : ℝ) := by
    rw [lsum_cast, lsum_cast, ← Finset.sum_add_distrib]; unfold spanVal
    exact Finset.sum_le_sum fun t ht => by rw [(hcr _).2]; exact hhi t (Finset.mem_range.mp ht)
  have hh1 : ((lsum B.center i s : ℚ) : ℝ) - ((lsum B.half i s : ℚ) : ℝ) ≤ ((lsum gh i s : ℚ) : ℝ) := by
    rw [lsum_cast, lsum_cast, lsum_cast, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun t ht => by
      rw [(hcr _).1]; exact_mod_cast (hin (i + t) (by have := Finset.mem_range.mp ht; omega)).1
  have hh2 : ((lsum gh i s : ℚ) : ℝ) ≤ ((lsum B.center i s : ℚ) : ℝ) + ((lsum B.half i s : ℚ) : ℝ) := by
    rw [lsum_cast, lsum_cast, lsum_cast, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun t ht => by
      rw [(hcr _).2]; exact_mod_cast (hin (i + t) (by have := Finset.mem_range.mp ht; omega)).2
  have hr0 : (0 : ℚ) ≤ lsum B.half i s := by
    have : (0 : ℝ) ≤ ((lsum B.half i s : ℚ) : ℝ) := by linarith
    exact_mod_cast this
  have hsbs := spanBounds_sound sd (lsum B.center i s) (lsum B.half i s) hr0 hsb
  have hT := taylor2_minorant (w := wK) (w1 := fun x => 2 * kCos x * kCos1 x) (w2 := wK2)
    (p := (((spanBounds sd (lsum B.center i s) (lsum B.half i s)).2.1 : ℚ) : ℝ))
    hasDerivAt_wK hasDerivAt_wK1 (fun ξ hξ => (hsbs ξ hξ).1) (x := spanVal g i s) ⟨hx1, hx2⟩
    (t := ((lsum gh i s : ℚ) : ℝ)) ⟨hh1, hh2⟩
  obtain ⟨hk0, hk1, -⟩ := KPt.sound sd.h
  rw [hhx] at hk0 hk1
  have hsq := (QI.contains_sq hk0).1
  have hwd := QI.contains_smul (2 * γ) (QI.contains_mul hk0 hk1)
  set xh : ℝ := ((lsum gh i s : ℚ) : ℝ) with hxh
  set x : ℝ := spanVal g i s with hx
  set p : ℚ := (spanBounds sd (lsum B.center i s) (lsum B.half i s)).2.1 with hp
  set w1 : ℝ := 2 * kCos xh * kCos1 xh with hw1
  have hwd' : (((2 * γ : ℚ)) : ℝ) * (kCos xh * kCos1 xh) = (γ : ℝ) * w1 := by rw [hw1]; push_cast; ring
  rw [hwd'] at hwd
  have hdiff : ∑ l ∈ Finset.range D.d, (if i ≤ l ∧ l < i + s then vv gh g l else 0) = x - xh := by
    rw [span_sum _ _ _ hsd, hx, hxh, lsum_cast]; unfold spanVal vv; rw [Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_, fun l => G l + (if i ≤ l ∧ l < i + s then (γ : ℝ) * w1 else 0), ?_, ?_⟩
  · simp only [cvxSpan, List.length_map, List.length_range]; exact hgl
  · simp only [cvxSpan, List.length_map, List.length_range]; exact hPl
  · intro a ha
    simp only [cvxSpan]
    rw [getD_range_map _ _ (by rw [hPl]; exact ha)]; simp [hPl]
  · intro a ha b hb
    simp only [cvxSpan]
    rw [getD_range_map _ _ (by rw [hPl]; exact ha), getD_range_map _ _ (by rw [hPl]; exact hb),
      getD_range_map _ _ (by rw [hPl]; exact hb), getD_range_map _ _ (by rw [hPl]; exact ha),
      hsym a ha b hb, Bool.and_comm]
  · intro l hl
    simp only [cvxSpan]
    rw [getD_range_map _ _ (by rw [hgl]; exact hl)]
    by_cases hS : i ≤ l ∧ l < i + s
    · simp only [hS, decide_true, if_true, and_self]
      exact QI.contains_add (hG l hl) hwd
    · simp only [hS, decide_false, if_false, add_zero]
      exact hG l hl
  · have hP' : ∀ a < D.d, ∀ b < D.d,
        (((cvxSpan B.center B.half gh acc (i, s, γ) sd).P.getD a []).getD b 0) =
          (acc.P.getD a []).getD b 0 + (if (i ≤ a ∧ a < i + s) ∧ (i ≤ b ∧ b < i + s) then γ * p else 0) := by
      intro a ha b hb
      simp only [cvxSpan]
      rw [getD_range_map _ _ (by rw [hPl]; exact ha), getD_range_map _ _ (by rw [hPl]; exact hb)]
      simp only [Bool.and_eq_true, decide_eq_true_eq, hp]
    rw [qf_update acc.P _ D.d i s (vv gh g) (γ * p) hP', gradsum_update, hdiff]
    have hF : (((cvxSpan B.center B.half gh acc (i, s, γ) sd).Flo : ℚ) : ℝ) =
        ((acc.Flo : ℚ) : ℝ) + (γ : ℝ) * (((QI.sq sd.h.k0).lo : ℚ) : ℝ) := by
      simp only [cvxSpan]; push_cast; ring
    rw [hF]
    have hγR : (0 : ℝ) ≤ γ := by exact_mod_cast hγ
    have hkey : (γ : ℝ) * ((((QI.sq sd.h.k0).lo : ℚ) : ℝ) + w1 * (x - xh) + (p : ℝ) / 2 * (x - xh) ^ 2) ≤
        (γ : ℝ) * wK x := by
      apply mul_le_mul_of_nonneg_left _ hγR
      have : wK xh = kCos xh ^ 2 := rfl
      linarith
    push_cast
    nlinarith [hkey, hineq]

private lemma ok_mono (c h gh : List ℚ) : ∀ (L : List ((ℕ × ℕ × ℚ) × SpanD)) (acc : CAcc),
    (L.foldl (fun a t => cvxSpan c h gh a t.1 t.2) acc).ok = true → acc.ok = true
  | [], _, hh => hh
  | t :: L, acc, hh => by
    have := ok_mono c h gh L _ hh
    simp only [cvxSpan, Bool.and_eq_true] at this
    exact this.1.1

private lemma fold_inv {D : LIQ} {B : Box} {gh : List ℚ} {g : ℕ → ℝ} (hg : B.Mem D.d g)
    (hin : ∀ l < D.d, (B.getD l (0, 0)).1 ≤ gh.getD l 0 ∧ gh.getD l 0 ≤ (B.getD l (0, 0)).2)
    (hsp : ∀ sp ∈ D.spans, 0 ≤ sp.2.2 ∧ sp.1 + sp.2.1 ≤ D.d) :
    ∀ (L : List ((ℕ × ℕ × ℚ) × SpanD)) (acc : CAcc) (Fp : ℝ), (∀ t ∈ L, t.1 ∈ D.spans) →
      Inv D gh g acc Fp →
      (L.foldl (fun a t => cvxSpan B.center B.half gh a t.1 t.2) acc).ok = true →
      Inv D gh g (L.foldl (fun a t => cvxSpan B.center B.half gh a t.1 t.2) acc)
        (Fp + (L.map fun t => (t.1.2.2 : ℝ) * wK (spanVal g t.1.1 t.1.2.1)).sum)
  | [], acc, Fp, _, hI, _ => by simpa using hI
  | t :: L, acc, Fp, hL, hI, hok => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons] at hok ⊢
    have hok1 := ok_mono B.center B.half gh L _ hok
    obtain ⟨⟨i, s, γ⟩, sd⟩ := t
    have ht := hsp _ (hL _ (List.mem_cons_self ..))
    have hI1 := step hg hin i s γ ht.1 ht.2 sd acc Fp hI hok1
    have := fold_inv hg hin hsp L _ _ (fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')) hI1 hok
    rwa [add_assoc] at this

theorem checkConvex_sound {D : LIQ} (hwf : D.wf = true) {B : Box} {gh : List ℚ} {sds : List SpanD}
    (h : checkConvex D B gh sds = true) {g : ℕ → ℝ} (hg0 : ∀ l, 0 ≤ g l) (hg : B.Mem D.d g) :
    ((D.claim : ℚ) : ℝ) ≤ D.F g := by
  have hwf2 := hwf
  simp only [LIQ.wf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf2
  obtain ⟨⟨hsp0, hmu⟩, hmul⟩ := hwf2
  have hsp : ∀ sp ∈ D.spans, 0 ≤ sp.2.2 ∧ sp.1 + sp.2.1 ≤ D.d := fun sp h => ⟨(hsp0 sp h).1.1, (hsp0 sp h).2⟩
  simp only [checkConvex, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hin, hok⟩, hlen⟩, hpsd⟩, hcl⟩ := h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hin
  -- initial invariant
  have hI0 : Inv D gh g ⟨((List.range D.d).map fun l => D.mu.getD l 0 * gh.getD l 0).sum,
      D.mu.map QI.pt, (List.range D.d).map (fun _ => (List.range D.d).map fun _ => 0), true⟩
      (∑ l ∈ Finset.range D.d, ((D.mu.getD l 0 : ℚ) : ℝ) * g l) := by
    refine ⟨by simp [hmul], by simp, fun a ha => by rw [getD_range_map _ _ ha]; simp,
      fun a ha b hb => by rw [getD_range_map _ _ ha, getD_range_map _ _ hb, getD_range_map _ _ hb,
        getD_range_map _ _ ha], fun l => ((D.mu.getD l 0 : ℚ) : ℝ), fun l hl => ?_, ?_⟩
    · have e : (D.mu.map QI.pt).getD l (QI.pt 0) = QI.pt (D.mu.getD l 0) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
        cases D.mu[l]? <;> rfl
      rw [e]; exact ⟨le_rfl, le_rfl⟩
    · have hq0 : qf ((List.range D.d).map (fun _ => (List.range D.d).map fun _ => (0 : ℚ))) D.d (vv gh g) = 0 := by
        unfold qf
        refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => ?_
        rw [getD_range_map _ _ (Finset.mem_range.mp ha), getD_range_map _ _ (Finset.mem_range.mp hb)]; simp
      rw [hq0, lrs]
      push_cast
      unfold vv
      rw [← Finset.sum_add_distrib]
      apply le_of_eq
      simp only [zero_div, add_zero]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
  have hI := fold_inv hg hin hsp (D.spans.zip sds) _ _ (fun t ht => (List.of_mem_zip ht).1) hI0 hok
  obtain ⟨-, hPl, hrows, hsym, G, hG, hineq⟩ := hI
  set acc := (D.spans.zip sds).foldl (fun a t => cvxSpan B.center B.half gh a t.1 t.2)
    ⟨((List.range D.d).map fun l => D.mu.getD l 0 * gh.getD l 0).sum,
      D.mu.map QI.pt, (List.range D.d).map (fun _ => (List.range D.d).map fun _ => 0), true⟩ with hacc
  have hq := psdLDL_sound_symm D.d acc.P ⟨hPl, fun row hrow => by
      obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hrow
      have := hrows a (by rw [← hPl]; exact ha)
      rwa [List.getD_eq_getElem _ _ ha] at this⟩ hsym hpsd (vv gh g)
  have hqf : 0 ≤ qf acc.P D.d (vv gh g) := hq
  -- the interval correction
  have hcorr : (((((List.range D.d).map fun l =>
      (QI.mul (acc.grad.getD l (QI.pt 0)) ⟨(B.getD l (0, 0)).1 - gh.getD l 0, (B.getD l (0, 0)).2 - gh.getD l 0⟩).lo).sum
        : ℚ)) : ℝ) ≤ ∑ l ∈ Finset.range D.d, G l * vv gh g l := by
    rw [lrs]; push_cast
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' := Finset.mem_range.mp hl
    have hJ : (QI.mk ((B.getD l (0, 0)).1 - gh.getD l 0) ((B.getD l (0, 0)).2 - gh.getD l 0)).Contains (vv gh g l) := by
      unfold vv QI.Contains; push_cast
      exact ⟨by linarith [(hg l hl').1], by linarith [(hg l hl').2]⟩
    exact (QI.contains_mul (hG l hl') hJ).1
  -- the span part of F
  have hspans : ((D.spans.zip sds).map fun t => (t.1.2.2 : ℝ) * wK (spanVal g t.1.1 t.1.2.1)).sum =
      (D.spans.map fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2).sum := by
    have e : ((D.spans.zip sds).map fun t => (t.1.2.2 : ℝ) * wK (spanVal g t.1.1 t.1.2.1)) =
        ((D.spans.zip sds).map Prod.fst).map (fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2) := by
      rw [List.map_map]; rfl
    rw [e, List.map_fst_zip (by omega)]
  have hcl' := (Rat.cast_le (K := ℝ)).mpr hcl
  rw [Rat.cast_add] at hcl'
  rw [hspans] at hineq
  unfold LIQ.F
  linarith

end ZetaS.CertV2

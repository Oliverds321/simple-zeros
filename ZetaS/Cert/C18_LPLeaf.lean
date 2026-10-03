/-
lean_work/L5_2/v3/C18_LPLeaf.lean — track C node C18, proved by L5_2 (28 Sep 2026) against the FIXED checker
`CheckerCoreV3` (L1_1c, 11:23: `lpSpan` admits the tangent l3 at x̂ only if `sd.h.x = xh ∧ x0 − r ≤ xh ∧ xh ≤ x0 + r`).
Statement byte-identical to `lean_work/L1_1/nodes/C18_LPLeaf.lean` (`checkLP_sound`).
Guard assumed (the one line of CheckerLeaves.lean that differs from CheckerCore.lean):
    (sb.1 && (decide (y3 = 0) || (decide (sd.h.x = xh) && decide (x0 - r ≤ xh) && decide (xh ≤ x0 + r))) && …)
Against the unfixed `CheckerCore` the statement is false (cnodes/C18_Counterexample.lean).
Depends on: C02 (proved, L5_1), C08 (`hasDerivAt_wK`, `hasDerivAt_wK1`), C09 (`KPt.sound`), C13 (proved, L5_2),
C15 (`chord_minorant`), C16 (`tangentLine_sound`) — statements.
-/
import ZetaS.Cert.NodeDefs
import ZetaS.Cert.C02_QIOps
import ZetaS.Cert.C08_KCosDerivs
import ZetaS.Cert.C09_KEncl
import ZetaS.Cert.C13_SpanBounds
import ZetaS.Cert.C15_ChordMinorant
import ZetaS.Cert.C16_TangentLine

noncomputable section

open Set Finset

namespace ZetaS.CertV2

namespace C18aux

lemma list_sum_range (f : ℕ → ℚ) : ∀ s : ℕ,
    ((((List.range s).map f).sum : ℚ) : ℝ) = ∑ t ∈ Finset.range s, ((f t : ℚ) : ℝ)
  | 0 => by simp
  | s + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, Rat.cast_add, list_sum_range f s,
      Finset.sum_range_succ]
    simp

lemma lsum_cast (v : List ℚ) (i s : ℕ) :
    ((lsum v i s : ℚ) : ℝ) = ∑ t ∈ Finset.range s, ((v.getD (i + t) 0 : ℚ) : ℝ) := by
  unfold lsum; exact list_sum_range _ s

lemma center_getD : ∀ (B : Box) (k : ℕ), B.center.getD k 0 = ((B.getD k (0, 0)).1 + (B.getD k (0, 0)).2) / 2
  | [], k => by simp [Box.center]
  | p :: B, 0 => by simp [Box.center]
  | p :: B, k + 1 => by simpa [Box.center] using center_getD B k

lemma half_getD : ∀ (B : Box) (k : ℕ), B.half.getD k 0 = ((B.getD k (0, 0)).2 - (B.getD k (0, 0)).1) / 2
  | [], k => by simp [Box.half]
  | p :: B, 0 => by simp [Box.half]
  | p :: B, k + 1 => by simpa [Box.half] using half_getD B k

/-- the span value of any v inside the box lies in [x0 − r, x0 + r]. -/
lemma span_in (B : Box) (v : ℕ → ℝ) (i s : ℕ)
    (hv : ∀ t < s, (((B.getD (i + t) (0, 0)).1 : ℚ) : ℝ) ≤ v (i + t) ∧ v (i + t) ≤ (((B.getD (i + t) (0, 0)).2 : ℚ) : ℝ)) :
    ((lsum B.center i s : ℚ) : ℝ) - ((lsum B.half i s : ℚ) : ℝ) ≤ ∑ t ∈ Finset.range s, v (i + t) ∧
    ∑ t ∈ Finset.range s, v (i + t) ≤ ((lsum B.center i s : ℚ) : ℝ) + ((lsum B.half i s : ℚ) : ℝ) := by
  rw [lsum_cast, lsum_cast, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  constructor <;> refine Finset.sum_le_sum fun t ht => ?_ <;> rw [center_getD, half_getD] <;> push_cast <;>
    linarith [(hv t (Finset.mem_range.1 ht)).1, (hv t (Finset.mem_range.1 ht)).2]

lemma addOn_length (rho : List ℚ) (i s : ℕ) (v : ℚ) : (addOn rho i s v).length = rho.length := by
  simp [addOn]

lemma addOn_getD (rho : List ℚ) (i s : ℕ) (v : ℚ) (l : ℕ) (hl : l < rho.length) :
    (addOn rho i s v).getD l 0 = rho.getD l 0 + (if i ≤ l ∧ l < i + s then v else 0) := by
  rw [List.getD_eq_getElem _ _ (by rw [addOn_length]; exact hl)]
  simp [addOn]

lemma sum_addOn (d : ℕ) (rho : List ℚ) (hlen : rho.length = d) (i s : ℕ) (hs : i + s ≤ d) (v : ℚ)
    (g : ℕ → ℝ) :
    ∑ l ∈ Finset.range d, (((addOn rho i s v).getD l 0 : ℚ) : ℝ) * g l =
      ∑ l ∈ Finset.range d, ((rho.getD l 0 : ℚ) : ℝ) * g l + (v : ℝ) * ∑ t ∈ Finset.range s, g (i + t) := by
  have e1 : ∀ l ∈ Finset.range d, (((addOn rho i s v).getD l 0 : ℚ) : ℝ) * g l =
      ((rho.getD l 0 : ℚ) : ℝ) * g l + (if i ≤ l ∧ l < i + s then (v : ℝ) * g l else 0) := by
    intro l hl
    rw [addOn_getD rho i s v l (by rw [hlen]; exact Finset.mem_range.1 hl)]
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.sum_filter]
  congr 1
  have hf : (Finset.range d).filter (fun l => i ≤ l ∧ l < i + s) = Finset.Ico i (i + s) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hf, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Finset.mul_sum]

lemma minLin_le (c lo hi : ℚ) (x : ℝ) (h1 : (lo : ℝ) ≤ x) (h2 : x ≤ (hi : ℝ)) :
    ((minLin c lo hi : ℚ) : ℝ) ≤ (c : ℝ) * x := by
  unfold minLin; push_cast
  rcases le_total 0 (c : ℝ) with hc | hc
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left h1 hc)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left h2 hc)

lemma boxMinLin_le (rho : List ℚ) (B : Box) (g : ℕ → ℝ)
    (hg : ∀ l < rho.length, (((B.getD l (0, 0)).1 : ℚ) : ℝ) ≤ g l ∧ g l ≤ (((B.getD l (0, 0)).2 : ℚ) : ℝ)) :
    ((boxMinLin rho B : ℚ) : ℝ) ≤ ∑ l ∈ Finset.range rho.length, ((rho.getD l 0 : ℚ) : ℝ) * g l := by
  unfold boxMinLin; rw [list_sum_range]
  exact Finset.sum_le_sum fun l hl => minLin_le _ _ _ _ (hg l (Finset.mem_range.1 hl)).1
    (hg l (Finset.mem_range.1 hl)).2

lemma spanBounds_c {sd : SpanD} {x0 r : ℚ} (h : (spanBounds sd x0 r).1 = true) : sd.c.x = x0 := by
  unfold spanBounds at h
  rcases hcl : sd.cells with _ | ⟨c0, rest⟩
  · simp only [hcl, decide_eq_true_eq] at h; exact h
  · simp only [hcl, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1.1

/-- w = kCos² ≥ its stored lower bound at a record. -/
lemma wlo_le (p : KPt) : (((QI.sq p.k0).lo : ℚ) : ℝ) ≤ wK p.x := by
  have := QI.contains_sq (KPt.sound p).1
  unfold wK; exact this.1

/-- line 4 (the chord) is a minorant of w on the whole span interval (for ANY rounded slope slq). -/
lemma chord_line (sd : SpanD) (x0 r : ℚ) (hr : 0 ≤ r) (hsb : (spanBounds sd x0 r).1 = true)
    (ha : sd.a.x = x0 - r) (hb : sd.b.x = x0 + r) (slp slq : ℚ)
    (hslp : slp = if r = 0 then 0 else ((QI.sq sd.b.k0).lo - (QI.sq sd.a.k0).lo) / (2 * r))
    (x : ℝ) (hx : x ∈ Icc ((x0 : ℝ) - r) (x0 + r)) :
    (slq : ℝ) * x + ((((QI.sq sd.a.k0).lo - slq * (x0 - r) - qabs (slp - slq) * 2 * r -
        max (spanBounds sd x0 r).2.2.1 0 * (2 * r) ^ 2 / 8 : ℚ)) : ℝ) ≤ wK x := by
  set wa := (QI.sq sd.a.k0).lo
  set wb := (QI.sq sd.b.k0).lo
  set q := (spanBounds sd x0 r).2.2.1
  have hwa : (wa : ℝ) ≤ wK ((x0 : ℝ) - r) := by
    have := wlo_le sd.a; rw [ha] at this; push_cast at this; exact this
  have hwb : (wb : ℝ) ≤ wK ((x0 : ℝ) + r) := by
    have := wlo_le sd.b; rw [hb] at this; push_cast at this; exact this
  have habs : ((qabs (slp - slq) : ℚ) : ℝ) = |(slp : ℝ) - slq| := by
    unfold qabs; split_ifs with h
    · have : (slp : ℝ) - slq < 0 := by exact_mod_cast h
      rw [abs_of_neg this]; push_cast; ring
    · have : 0 ≤ (slp : ℝ) - slq := by exact_mod_cast not_lt.1 h
      rw [abs_of_nonneg this]; push_cast; ring
  have hxa : 0 ≤ x - ((x0 : ℝ) - r) := by linarith [hx.1]
  have hxb : x - ((x0 : ℝ) - r) ≤ 2 * r := by linarith [hx.2]
  have hmq : (0 : ℝ) ≤ max (q : ℝ) 0 := le_max_right _ _
  push_cast
  rw [habs]
  have hdiff : (slq : ℝ) * (x - ((x0 : ℝ) - r)) - |(slp : ℝ) - slq| * 2 * r ≤ (slp : ℝ) * (x - ((x0 : ℝ) - r)) := by
    have h1 : ((slq : ℝ) - slp) * (x - ((x0 : ℝ) - r)) ≤ |(slp : ℝ) - slq| * (x - ((x0 : ℝ) - r)) :=
      mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) hxa
    have h2 : |(slp : ℝ) - slq| * (x - ((x0 : ℝ) - r)) ≤ |(slp : ℝ) - slq| * (2 * r) :=
      mul_le_mul_of_nonneg_left hxb (abs_nonneg _)
    nlinarith
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · -- r = 0: the interval is a point
    have hr0' : (r : ℝ) = 0 := by exact_mod_cast hr0.symm
    have hxx : x = (x0 : ℝ) - r := by linarith [hx.1, hx.2]
    rw [hr0'] at hwa hxx ⊢
    rw [hxx]
    have : (slq : ℝ) * ((x0 : ℝ) - 0) + ((wa : ℝ) - slq * ((x0 : ℝ) - 0) - |(slp : ℝ) - slq| * 2 * 0 -
        max (q : ℝ) 0 * (2 * 0) ^ 2 / 8) = wa := by ring
    rw [this]; simpa using hwa
  · have hrr : (0 : ℝ) < r := by exact_mod_cast hrpos
    have hslp : (slp : ℝ) = ((wb : ℝ) - wa) / (2 * r) := by
      rw [hslp, if_neg hrpos.ne']; push_cast; ring
    have hq : ∀ ξ ∈ Icc ((x0 : ℝ) - r) (x0 + r), wK2 ξ ≤ (q : ℝ) := fun ξ hξ =>
      (spanBounds_sound sd x0 r hr hsb ξ hξ).2.1
    have hch := chord_minorant (w := wK) (w1 := fun x => 2 * kCos x * kCos1 x) (w2 := wK2)
      (by linarith : (x0 : ℝ) - r < x0 + r) hasDerivAt_wK hasDerivAt_wK1 hq hx
    have hba : ((x0 : ℝ) + r) - (x0 - r) = 2 * r := by ring
    rw [hba] at hch
    set τ := (x - ((x0 : ℝ) - r)) / (2 * r)
    have hτ0 : 0 ≤ τ := div_nonneg hxa (by linarith)
    have hτ1 : τ ≤ 1 := by rw [div_le_one (by linarith)]; exact hxb
    have e1 : (slp : ℝ) * (x - ((x0 : ℝ) - r)) = ((wb : ℝ) - wa) * τ := by rw [hslp]; ring
    have e2 : (wK ((x0 : ℝ) + r) - wK (x0 - r)) / (2 * r) * (x - (x0 - r)) =
        (wK ((x0 : ℝ) + r) - wK (x0 - r)) * τ := by ring
    rw [e2] at hch
    have h3 : (wa : ℝ) + ((wb : ℝ) - wa) * τ ≤ wK ((x0 : ℝ) - r) + (wK ((x0 : ℝ) + r) - wK (x0 - r)) * τ := by
      nlinarith
    nlinarith

lemma mul_line {y L W : ℝ} (hy : 0 ≤ y) (h : y ≠ 0 → L ≤ W) : y * L ≤ y * W := by
  rcases eq_or_lt_of_le hy with h0 | hpos
  · rw [← h0]; simp
  · exact mul_le_mul_of_nonneg_left (h hpos.ne') hy

/-- value of an accumulator at g. -/
def V (d : ℕ) (g : ℕ → ℝ) (a : Acc) : ℝ := (a.kap : ℝ) + ∑ l ∈ Finset.range d, ((a.rho.getD l 0 : ℚ) : ℝ) * g l

/-- **one span of an LP leaf**: the added lines are, together, below γ′ w(span value) on the box. -/
lemma lpSpan_step (D : LIQ) (hwf : D.wf = true) (B : Box) (gh : List ℚ) (g : ℕ → ℝ) (hg : B.Mem D.d g)
    (a : Acc) (hlen : a.rho.length = D.d) (sp : ℕ × ℕ × ℚ) (hsp : sp ∈ D.spans)
    (sd : SpanD) (yy : List ℚ) (hok : (lpSpan B.center B.half gh a sp sd yy).ok = true) :
    a.ok = true ∧ (lpSpan B.center B.half gh a sp sd yy).rho.length = D.d ∧
    V D.d g (lpSpan B.center B.half gh a sp sd yy) ≤
      V D.d g a + ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2 := by
  obtain ⟨i, s, γ⟩ := sp
  unfold LIQ.wf at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  obtain ⟨⟨hγ, -⟩, his⟩ := hwf.1.1 _ hsp
  simp only at hγ his
  have hsx := span_in B g i s (fun t ht => hg (i + t) (by omega))
  set x0 := lsum B.center i s
  set r := lsum B.half i s
  set xh := lsum gh i s
  have hr : 0 ≤ r := by
    have : (0 : ℝ) ≤ (r : ℝ) := by linarith [hsx.1, hsx.2]
    exact_mod_cast this
  set x := spanVal g i s with hxdef
  have hxI : x ∈ Icc ((x0 : ℝ) - r) (x0 + r) := ⟨hsx.1, hsx.2⟩
  have hw0 : 0 ≤ wK x := by unfold wK; positivity
  set sb := spanBounds sd x0 r
  set pen := max 0 (-sb.2.1)
  set l2 := tangentLine x0 r x0 pen sd.c
  set l3 := tangentLine x0 r xh pen sd.h
  set wa := (QI.sq sd.a.k0).lo
  set wb := (QI.sq sd.b.k0).lo
  set slp : ℚ := if r = 0 then 0 else (wb - wa) / (2 * r)
  set slq := QI.rdn slp
  set l4 : ℚ × ℚ := (slq, wa - slq * (x0 - r) - (qabs (slp - slq)) * 2 * r - max sb.2.2.1 0 * (2 * r) ^ 2 / 8)
  set y0 := yy.getD 0 0
  set y1 := yy.getD 1 0
  set y2 := yy.getD 2 0
  set y3 := yy.getD 3 0
  set y4 := yy.getD 4 0
  have e : lpSpan B.center B.half gh a (i, s, γ) sd yy =
      ⟨addOn a.rho i s (y2 * l2.1 + y3 * l3.1 + y4 * l4.1),
       a.kap + y1 * sb.2.2.2 + y2 * l2.2 + y3 * l3.2 + y4 * l4.2,
       a.ok && ((decide (y1 = 0 ∧ y2 = 0 ∧ y3 = 0 ∧ y4 = 0) ||
          (sb.1 && (decide (y3 = 0) || (decide (sd.h.x = xh) && decide (x0 - r ≤ xh) && decide (xh ≤ x0 + r))) &&
            (decide (y4 = 0) || (decide (sd.a.x = x0 - r) && decide (sd.b.x = x0 + r))))) &&
        decide (0 ≤ y0 ∧ 0 ≤ y1 ∧ 0 ≤ y2 ∧ 0 ≤ y3 ∧ 0 ≤ y4) && decide (y0 + y1 + y2 + y3 + y4 ≤ γ))⟩ := rfl
  rw [e] at hok ⊢
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨haok, ⟨hcase, hy0, hy1, hy2, hy3, hy4⟩, hsum⟩ := hok
  refine ⟨haok, by simp only; rw [addOn_length, hlen], ?_⟩
  unfold V
  simp only
  rw [sum_addOn D.d a.rho hlen i s his]
  have hγ' : (0 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hsum' : (y0 : ℝ) + y1 + y2 + y3 + y4 ≤ γ := by exact_mod_cast hsum
  have hy' : (0 : ℝ) ≤ y0 ∧ (0 : ℝ) ≤ y1 ∧ (0 : ℝ) ≤ y2 ∧ (0 : ℝ) ≤ y3 ∧ (0 : ℝ) ≤ y4 :=
    ⟨by exact_mod_cast hy0, by exact_mod_cast hy1, by exact_mod_cast hy2, by exact_mod_cast hy3,
      by exact_mod_cast hy4⟩
  have hx' : ∑ t ∈ Finset.range s, g (i + t) = x := rfl
  rw [hx']
  -- the key inequality  K + v·x ≤ γ w(x)
  suffices key : (y1 : ℝ) * sb.2.2.2 + y2 * ((l2.1 : ℝ) * x + l2.2) + y3 * ((l3.1 : ℝ) * x + l3.2) +
      y4 * ((l4.1 : ℝ) * x + l4.2) ≤ γ * wK x by
    have ew : wK x = kCos x ^ 2 := rfl
    rw [← ew]; push_cast; nlinarith
  rcases hcase with ⟨z1, z2, z3, z4⟩ | ⟨⟨hsb, h3⟩, h4⟩
  · rw [z1, z2, z3, z4]; push_cast; nlinarith
  · have hsbs := spanBounds_sound sd x0 r hr hsb
    have hcx := spanBounds_c hsb
    have hpen0 : (0 : ℚ) ≤ pen := le_max_left _ _
    have hpen : ∀ ξ ∈ Icc ((x0 : ℝ) - r) (x0 + r), -((pen : ℚ) : ℝ) ≤ wK2 ξ := by
      intro ξ hξ
      have := (hsbs ξ hξ).1
      have hp : -sb.2.1 ≤ pen := le_max_right _ _
      have hp' : -((sb.2.1 : ℚ) : ℝ) ≤ ((pen : ℚ) : ℝ) := by exact_mod_cast hp
      linarith
    have L1 : ((sb.2.2.2 : ℚ) : ℝ) ≤ wK x := (hsbs x hxI).2.2
    have L2 : (l2.1 : ℝ) * x + l2.2 ≤ wK x :=
      tangentLine_sound x0 r x0 pen sd.c hcx ⟨by linarith, by linarith⟩ hpen0 hpen x hxI
    have L3 : y3 ≠ 0 → (l3.1 : ℝ) * x + l3.2 ≤ wK x := by
      intro hy
      rcases h3 with h3 | ⟨⟨hh, hlo⟩, hhi⟩
      · exact absurd h3 hy
      · exact tangentLine_sound x0 r xh pen sd.h hh ⟨hlo, hhi⟩ hpen0 hpen x hxI
    have L4 : y4 ≠ 0 → (l4.1 : ℝ) * x + l4.2 ≤ wK x := by
      intro hy
      rcases h4 with h4 | ⟨ha, hb⟩
      · exact absurd h4 hy
      · exact chord_line sd x0 r hr hsb ha hb slp slq rfl x hxI
    have m1 := mul_le_mul_of_nonneg_left L1 hy'.2.1
    have m2 := mul_le_mul_of_nonneg_left L2 hy'.2.2.1
    have m3 := mul_line hy'.2.2.2.1 (fun h => L3 (by exact_mod_cast h))
    have m4 := mul_line hy'.2.2.2.2 (fun h => L4 (by exact_mod_cast h))
    nlinarith [mul_nonneg hy'.1 hw0]

lemma fold_step (D : LIQ) (hwf : D.wf = true) (B : Box) (gh : List ℚ) (g : ℕ → ℝ) (hg : B.Mem D.d g) :
    ∀ (L : List (((ℕ × ℕ × ℚ) × SpanD) × List ℚ)) (a : Acc), (∀ t ∈ L, t.1.1 ∈ D.spans) →
      a.rho.length = D.d →
      (L.foldl (fun a t => lpSpan B.center B.half gh a t.1.1 t.1.2 t.2) a).ok = true →
      a.ok = true ∧ (L.foldl (fun a t => lpSpan B.center B.half gh a t.1.1 t.1.2 t.2) a).rho.length = D.d ∧
      V D.d g (L.foldl (fun a t => lpSpan B.center B.half gh a t.1.1 t.1.2 t.2) a) ≤
        V D.d g a + (L.map fun t => ((t.1.1.2.2 : ℚ) : ℝ) * kCos (spanVal g t.1.1.1 t.1.1.2.1) ^ 2).sum
  | [], a, _, hlen, hok => by simpa using ⟨hok, hlen⟩
  | t :: L, a, hmem, hlen, hok => by
    simp only [List.foldl_cons] at hok ⊢
    have hstep := lpSpan_step D hwf B gh g hg a hlen t.1.1 (hmem t (List.mem_cons_self ..)) t.1.2 t.2
    obtain ⟨h1, h2, h3⟩ := fold_step D hwf B gh g hg L _ (fun u hu => hmem u (List.mem_cons_of_mem _ hu))
      (by
        -- the length is preserved by one step (addOn)
        show (addOn a.rho _ _ _).length = D.d
        rw [addOn_length, hlen]) hok
    obtain ⟨h4, -, h5⟩ := hstep h1
    refine ⟨h4, h2, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    linarith

lemma chunks5_length : ∀ (n : ℕ) (y : List ℚ), y.length = 5 * n + 1 → (chunks5 y).length = n
  | 0, y, h => by
    rcases y with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at h
    · rfl
    · simp at h
  | n + 1, y, h => by
    rcases y with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
    · simp at h
    · simp at h
    · simp at h <;> omega
    · simp at h <;> omega
    · simp at h <;> omega
    · simp only [List.length_cons] at h
      simp only [chunks5, List.length_cons]
      rw [chunks5_length n rest (by omega)]

end C18aux

open C18aux in
theorem checkLP_sound {D : LIQ} (hwf : D.wf = true) {B : Box} {gh y : List ℚ} {sds : List SpanD}
    (h : checkLP D B gh y sds = true) {g : ℕ → ℝ} (hg0 : ∀ l, 0 ≤ g l) (hg : B.Mem D.d g) :
    ((D.claim : ℚ) : ℝ) ≤ D.F g := by
  have hwf' := hwf
  unfold LIQ.wf at hwf'
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf'
  obtain ⟨⟨hsp, hmu⟩, hmulen⟩ := hwf'
  set lam := y.getLastD 0
  set acc0 : Acc := ⟨D.mu.map (fun m => m * (1 + lam)), -lam * D.claim, decide (0 ≤ lam)⟩
  set L := (D.spans.zip sds).zip (chunks5 y)
  set acc := L.foldl (fun a t => lpSpan B.center B.half gh a t.1.1 t.1.2 t.2) acc0
  have e : checkLP D B gh y sds = (acc.ok && decide (sds.length = D.spans.length) &&
      decide (y.length = 5 * D.spans.length + 1) && decide (D.claim ≤ acc.kap + boxMinLin acc.rho B)) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hl1⟩, hl2⟩, hcl⟩ := h
  have hmemL : ∀ t ∈ L, t.1.1 ∈ D.spans := by
    intro t ht
    exact (List.of_mem_zip (List.of_mem_zip ht).1).1
  have hlen0 : acc0.rho.length = D.d := by simp [acc0, hmulen]
  obtain ⟨hok0, hlenA, hV⟩ := fold_step D hwf B gh g hg L acc0 hmemL hlen0 hok
  have hlam : (0 : ℚ) ≤ lam := by simpa [acc0] using hok0
  have hlam' : (0 : ℝ) ≤ lam := by exact_mod_cast hlam
  -- the spans of L are exactly D.spans
  have hmap : L.map (fun t => t.1.1) = D.spans := by
    have hc := chunks5_length D.spans.length y hl2
    have h1 : (D.spans.zip sds).map Prod.fst = D.spans := List.map_fst_zip (by omega)
    have h2 : L.map Prod.fst = D.spans.zip sds := List.map_fst_zip (by simp [List.length_zip, hc, hl1])
    rw [show (fun t : ((ℕ × ℕ × ℚ) × SpanD) × List ℚ => t.1.1) = Prod.fst ∘ Prod.fst from rfl,
      ← List.map_map, h2, h1]
  have hsumL : (L.map fun t => ((t.1.1.2.2 : ℚ) : ℝ) * kCos (spanVal g t.1.1.1 t.1.1.2.1) ^ 2).sum =
      (D.spans.map fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2).sum := by
    rw [← hmap, List.map_map]; rfl
  rw [hsumL] at hV
  set S := (D.spans.map fun sp => ((sp.2.2 : ℚ) : ℝ) * kCos (spanVal g sp.1 sp.2.1) ^ 2).sum
  have hS : 0 ≤ S := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨sp, hsp', rfl⟩ := List.mem_map.1 hz
    have := (hsp sp hsp').1.1
    have : (0 : ℝ) ≤ ((sp.2.2 : ℚ) : ℝ) := by exact_mod_cast this
    positivity
  -- claim ≤ V(acc)
  have hbox := boxMinLin_le acc.rho B g (fun l hl => hg l (by rw [hlenA] at hl; exact hl))
  rw [hlenA] at hbox
  have hcl' : ((D.claim : ℚ) : ℝ) ≤ (acc.kap : ℝ) + ((boxMinLin acc.rho B : ℚ) : ℝ) := by exact_mod_cast hcl
  have hVacc : ((D.claim : ℚ) : ℝ) ≤ V D.d g acc := by unfold V; linarith
  -- V(acc0)
  set M := ∑ l ∈ Finset.range D.d, ((D.mu.getD l 0 : ℚ) : ℝ) * g l
  have hV0 : V D.d g acc0 = -(lam : ℝ) * D.claim + (1 + lam) * M := by
    unfold V
    simp only [acc0]
    have : ∀ l, ((D.mu.map (fun m => m * (1 + lam))).getD l 0) = D.mu.getD l 0 * (1 + lam) := by
      intro l
      have := List.getD_map (fun m : ℚ => m * (1 + lam)) (l := D.mu) (n := l) (d := 0)
      simpa using this
    simp only [this]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hF : D.F g = S + M := rfl
  rw [hF]
  have key : (1 + (lam : ℝ)) * (((D.claim : ℚ) : ℝ) - M - S) ≤ -(lam : ℝ) * S := by nlinarith
  have : ((D.claim : ℚ) : ℝ) - M - S ≤ 0 := by
    by_contra hc
    push Not at hc
    have : 0 < (1 + (lam : ℝ)) * (((D.claim : ℚ) : ℝ) - M - S) := mul_pos (by linarith) hc
    nlinarith
  linarith

end ZetaS.CertV2

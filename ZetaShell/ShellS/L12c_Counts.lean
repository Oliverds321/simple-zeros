/-
L7_12c (3 Oct 2026): Lemma 6d (lem:shell-6d), the zero counts fed into the block lemma `L12c_family`:
* Jutila's / Bombieri's rectangle count `Nrect` (closed rectangle `σ ≤ β ≤ 1`, `|γ| ≤ Y`) bounds every finite set of
  nontrivial zeros with `β ≥ σ`, `|γ| ≤ Y` (`σ > 0`; the rectangle is a finite set: no zeros on `β = 1`);
* all nontrivial zeros with `|γ| ≤ Y`: `Σ m ≤ (2Y+2)·A₀(log r + log(Y+4))` (unit windows, `L12b_local_count`);
* the block sums: `Σ_{r∈S_i} Σ*_χ Nrect ≤ N*(⌊R_i⌋, σ, Y)` and `Σ_{r∈S_i} Σ*_χ (2Y+2)A₀(log r + log(Y+4)) ≤
  R_i²(2Y+2)A₀(log R_i + log(Y+4))`;
* the power form of the block lemma: if the block sums are `≤ C (R_i² 2^j H_i)^a` (`0 ≤ a ≤ 2`), then
  `W(P) ≤ (⌈1/ε′⌉+1)·9C·(𝒵 N₀^{2ε′})^a` (Lemma 6b/6c: `R_i² H_i ≤ 𝒵 N₀^{2ε′}`).
-/
import ZetaShell.ShellS.L12c_Family
import ZetaShell.ShellS.L12b_Z6a

noncomputable section
open Complex
open scoped ENNReal

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- the rectangle `σ ≤ β ≤ 1`, `|γ| ≤ Y` (`σ > 0`) holds finitely many zeros. -/
lemma L12c_rect_finite {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (σ Y : ℝ)
    (hσ : 0 < σ) : (zerosRect χ σ Y).Finite := by
  have hne : ∀ ρ : ℂ, 1 ≤ ρ.re → χ.LFunction ρ ≠ 0 := by
    intro ρ hρ
    rcases Nat.lt_or_ge 1 r with hr | hr
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
        (.inl (Zeta23.ThmE.ne_one_of_primitive hr hχ)) hρ
    · have h1 : r = 1 := le_antisymm hr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
      subst h1
      rw [DirichletCharacter.LFunction_modOne_eq]
      exact riemannZeta_ne_zero_of_one_le_re hρ
  have hsub : zerosRect χ σ Y ⊆ {ρ | IsNtZero χ ρ} ∩ {ρ | -Y - 1 < ρ.im ∧ ρ.im ≤ Y} := by
    intro ρ hρ
    obtain ⟨h0, h1, h2, h3⟩ := hρ
    have hlt : ρ.re < 1 := by
      rcases lt_or_eq_of_le h2 with h | h
      · exact h
      · exact absurd h0 (hne ρ h.ge)
    have hab := abs_le.mp h3
    exact ⟨⟨h0, by linarith, hlt⟩, by linarith [hab.1], hab.2⟩
  apply Set.Finite.subset _ hsub
  rcases Nat.lt_or_ge 1 r with hr | hr
  · exact (Zeta23.ThmE.LSeam_of hr hχ).finite_window (-Y - 1) Y
  · have h1 : r = 1 := le_antisymm hr (Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
    subst h1
    have hL : χ.LFunction = riemannZeta := DirichletCharacter.LFunction_modOne_eq
    apply Set.Finite.subset (Zeta23.zetaZeroConfig.finite_window (-Y - 1) Y)
    intro ρ hρ
    obtain ⟨hz, hw⟩ := hρ
    refine ⟨?_, hw⟩
    show riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1
    rw [← hL]; exact hz

lemma L12c_Nrect_nonneg (r : ℕ) (χ : DirichletCharacter ℂ r) (σ Y : ℝ) : 0 ≤ Nrect r χ σ Y := by
  unfold Nrect; split_ifs <;> positivity

/-- finite sets of zeros with `β ≥ σ`, `|γ| ≤ Y` are counted by `Nrect`. -/
lemma L12c_rect_count {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (σ Y : ℝ)
    (hσ : 0 < σ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}) (hs : ∀ ρ ∈ s, σ ≤ ρ.1.re ∧ |ρ.1.im| ≤ Y) :
    ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ Nrect r χ σ Y := by
  classical
  have hfin := L12c_rect_finite χ hχ σ Y hσ
  unfold Nrect
  rw [dif_neg (NeZero.ne r)]
  unfold NrectC
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hsub : s.map (Function.Embedding.subtype _) ⊆ hfin.toFinset := by
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨ρ, hρ, rfl⟩ := hx
    rw [Set.Finite.mem_toFinset]
    exact ⟨ρ.2.1, (hs ρ hρ).1, ρ.2.2.2.le, (hs ρ hρ).2⟩
  have h := Finset.sum_le_sum_of_subset (f := fun ρ => zmult χ ρ) hsub
  rw [Finset.sum_map] at h
  exact_mod_cast h

/-- all nontrivial zeros with `|γ| ≤ Y`: `Σ m ≤ (2Y+2)A₀(log r + log(Y+4))`. -/
lemma L12c_all_count {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (t : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, t < ρ.1.im ∧ ρ.1.im ≤ t + 1) →
      ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₀ * (Real.log r + Real.log (|t| + 3)))
    (Y : ℝ) (hY : 0 ≤ Y) (s : Finset {ρ : ℂ // IsNtZero χ ρ}) (hs : ∀ ρ ∈ s, |ρ.1.im| ≤ Y) :
    ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ (2 * Y + 2) * (A₀ * (Real.log r + Real.log (Y + 4))) := by
  classical
  have hlr : 0 ≤ Real.log r :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne r))
  set γ₀ := -Y - 1 with hγ₀
  set Λ : ℝ → ℝ := fun t => A₀ * (Real.log r + Real.log (|t| + 3)) with hΛ
  have h := L12b_window_sum s (fun ρ => ρ.1.im) (fun ρ => (zmult χ ρ.1 : ℝ)) (fun _ => 1) Λ (fun _ => 1) γ₀
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => le_rfl) (fun _ => zero_le_one)
    (fun t s' _ hs' => hloc t s' hs')
  simp only [mul_one, one_mul] at h
  refine h.trans ?_
  set keys := s.image (fun ρ => ⌈ρ.1.im - γ₀⌉) with hkeys
  have hkey : ∀ k ∈ keys, 1 ≤ k ∧ k ≤ ⌈2 * Y + 1⌉ ∧ |γ₀ + k - 1| ≤ Y + 1 := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨ρ, hρ, rfl⟩ := hk
    have hab := abs_le.mp (hs ρ hρ)
    have hc := Int.ceil_eq_iff.mp (rfl : ⌈ρ.1.im - γ₀⌉ = ⌈ρ.1.im - γ₀⌉)
    refine ⟨?_, Int.ceil_mono (by rw [hγ₀]; linarith [hab.2]), ?_⟩
    · rw [Int.one_le_ceil_iff]; rw [hγ₀]; linarith [hab.1]
    · rw [abs_le]; constructor <;> linarith [hc.1, hc.2, hab.1, hab.2]
  have hΛle : ∀ k ∈ keys, Λ (γ₀ + k - 1) ≤ A₀ * (Real.log r + Real.log (Y + 4)) := by
    intro k hk
    simp only [hΛ]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have := (hkey k hk).2.2
    have h4 : Real.log (|γ₀ + k - 1| + 3) ≤ Real.log (Y + 4) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  have hcard : (keys.card : ℝ) ≤ 2 * Y + 2 := by
    have hsub : keys ⊆ Finset.Icc 1 ⌈2 * Y + 1⌉ := fun k hk => by
      rw [Finset.mem_Icc]; exact ⟨(hkey k hk).1, (hkey k hk).2.1⟩
    have h1 := Finset.card_le_card hsub
    rw [Int.card_Icc] at h1
    have h2 : ((⌈2 * Y + 1⌉ + 1 - 1).toNat : ℝ) ≤ 2 * Y + 2 := by
      simp only [add_sub_cancel_right]
      have h3 : (0 : ℤ) ≤ ⌈2 * Y + 1⌉ := Int.ceil_nonneg (by linarith)
      rw [show ((⌈2 * Y + 1⌉.toNat : ℕ) : ℝ) = ((⌈2 * Y + 1⌉ : ℤ) : ℝ) by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg h3]]
      linarith [Int.ceil_lt_add_one (2 * Y + 1)]
    calc (keys.card : ℝ) ≤ ((⌈2 * Y + 1⌉ + 1 - 1).toNat : ℝ) := by exact_mod_cast h1
      _ ≤ 2 * Y + 2 := h2
  have hpos : 0 ≤ A₀ * (Real.log r + Real.log (Y + 4)) := by
    have : 0 ≤ Real.log (Y + 4) := Real.log_nonneg (by linarith)
    positivity
  calc ∑ k ∈ keys, Λ (γ₀ + k - 1) ≤ ∑ k ∈ keys, A₀ * (Real.log r + Real.log (Y + 4)) :=
        Finset.sum_le_sum hΛle
    _ = keys.card * (A₀ * (Real.log r + Real.log (Y + 4))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Y + 2) * (A₀ * (Real.log r + Real.log (Y + 4))) := mul_le_mul_of_nonneg_right hcard hpos

/-- the block moduli lie in `[1, ⌊R_i⌋]`. -/
lemma L12cS_sub (Qn : ℕ) (T K ε s₀ ε' : ℝ) (i : ℕ) :
    L12cS Qn T K ε s₀ ε' i ⊆ Finset.Icc 1 ⌊Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i⌋₊ := by
  intro r hr
  unfold L12cS at hr
  rw [Finset.mem_filter, Finset.mem_Icc] at hr
  rw [Finset.mem_Icc]
  exact ⟨hr.1.1, Nat.le_floor hr.2.1⟩

/-- block sum of the rectangle counts `≤ N*(⌊R_i⌋, σ, Y)`. -/
lemma L12c_block_rect (Qn : ℕ) (T K ε s₀ ε' : ℝ) (i : ℕ) (σ Y : ℝ) :
    ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r, Nrect r χ σ Y
      ≤ Nstar ⌊Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i⌋₊ σ Y := by
  unfold Nstar
  exact Finset.sum_le_sum_of_subset_of_nonneg (L12cS_sub Qn T K ε s₀ ε' i)
    (fun r _ _ => Finset.sum_nonneg fun χ _ => L12c_Nrect_nonneg r χ σ Y)

/-- block sum of the all-zeros counts. -/
lemma L12c_block_all (Qn : ℕ) (T K ε s₀ ε' : ℝ) (i : ℕ) (A₀ Y : ℝ) (hA₀ : 0 ≤ A₀) (hY : 0 ≤ Y)
    (hRi : 1 ≤ Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i) :
    ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r, (2 * Y + 2) * (A₀ * (Real.log r + Real.log (Y + 4)))
      ≤ Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i ^ 2 * ((2 * Y + 2) *
          (A₀ * (Real.log (Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i) + Real.log (Y + 4)))) := by
  set R := Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i with hR
  have hl4 : 0 ≤ Real.log (Y + 4) := Real.log_nonneg (by linarith)
  have hpt : ∀ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r, (2 * Y + 2) * (A₀ * (Real.log r + Real.log (Y + 4)))
      ≤ R * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4)))) := by
    intro r hr
    have hr' := Finset.mem_filter.mp hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr'.1).1
    have hrR : (r : ℝ) ≤ R := hr'.2.1
    have : NeZero r := ⟨by omega⟩
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hlog : Real.log r ≤ Real.log R := Real.log_le_log hr0 hrR
    have hlr : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr1)
    have hcard := L12b_card_prim r
    have hφ : (Nat.totient r : ℝ) ≤ r := by exact_mod_cast Nat.totient_le r
    rw [Finset.sum_const, nsmul_eq_mul]
    apply mul_le_mul (hcard.trans (hφ.trans hrR)) _ (by positivity) (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply mul_le_mul_of_nonneg_left _ hA₀
    linarith
  have hcardS : ((L12cS Qn T K ε s₀ ε' i).card : ℝ) ≤ R := by
    have h1 := Finset.card_le_card (L12cS_sub Qn T K ε s₀ ε' i)
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    calc ((L12cS Qn T K ε s₀ ε' i).card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ R := Nat.floor_le (by linarith)
  have hX : 0 ≤ R * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4)))) := by
    have : 0 ≤ Real.log R := Real.log_nonneg hRi
    positivity
  calc _ ≤ ∑ r ∈ L12cS Qn T K ε s₀ ε' i, R * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4)))) :=
        Finset.sum_le_sum hpt
    _ = (L12cS Qn T K ε s₀ ε' i).card * (R * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4))))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R * (R * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4))))) := mul_le_mul_of_nonneg_right hcardS hX
    _ = R ^ 2 * ((2 * Y + 2) * (A₀ * (Real.log R + Real.log (Y + 4)))) := by ring

/-- **the block lemma in power form**: block sums `≤ C (R_i² 2^j H_i)^a` give
`W(P) ≤ (⌈1/ε′⌉+1)·9C·(𝒵 N₀^{2ε′})^a`. -/
theorem L12c_family_pow (Qn : ℕ) (T K ε s₀ ε' : ℝ) (k : ℕ) (hk : 3 ≤ k) (P : ℂ → Prop)
    (hT : 1 ≤ T) (hK : 0 ≤ K) (hQ : 0 < (Qn : ℝ)) (hs : 0 < s₀) (hR1 : 1 ≤ (R1S Qn ε s₀ : ℝ))
    (hR1N : (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀) (hε' : 0 < ε') (hε1 : ε' ≤ 1)
    (N : (r : ℕ) → DirichletCharacter ℂ r → ℝ → ℝ) (hN0 : ∀ r χ Y, 0 ≤ N r χ Y)
    (hN : ∀ r ∈ Finset.Icc 1 (R1S Qn ε s₀), ∀ χ ∈ primChars r, ∀ (h : r ≠ 0),
      haveI : NeZero r := ⟨h⟩;
      ∀ (Y : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, P ρ.1 ∧ |ρ.1.im| ≤ Y) →
        ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ N r χ Y)
    (C a : ℝ) (hC : 0 ≤ C) (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (hblock : ∀ i ≤ ⌈1 / ε'⌉₊, 1 ≤ Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i → ∀ j : ℕ,
      ∑ r ∈ L12cS Qn T K ε s₀ ε' i, ∑ χ ∈ primChars r,
        N r χ (2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i)
      ≤ C * (Rblk (R1S Qn ε s₀) (Real.exp s₀) ε' i ^ 2 *
          (2 ^ j * Hblk T K (Real.exp s₀) Qn (R1S Qn ε s₀) ε' i)) ^ a) :
    L12cW Qn T K ε s₀ k P ≤ ENNReal.ofReal ((⌈1 / ε'⌉₊ + 1) * (9 * C *
      (Zsize (R1S Qn ε s₀) T K (Real.exp s₀) Qn * Real.exp s₀ ^ (2 * ε')) ^ a)) := by
  classical
  set R₁ := R1S Qn ε s₀ with hR₁
  set N₀ := Real.exp s₀ with hN₀
  set Z := Zsize R₁ T K N₀ Qn * N₀ ^ (2 * ε') with hZ
  set F : ℕ → ℕ → ℝ := fun i j => if 1 ≤ Rblk R₁ N₀ ε' i then
    C * (Rblk R₁ N₀ ε' i ^ 2 * (2 ^ j * Hblk T K N₀ Qn R₁ ε' i)) ^ a else 0 with hF
  have hN0' : 1 < N₀ := by have := Real.add_one_le_exp s₀; linarith
  have hfam := L12c_family Qn T K ε s₀ ε' k P hT hK hQ hs hR1 hR1N hε' hε1 N hN0 hN F (by
    intro i hi j
    by_cases hRi : 1 ≤ Rblk R₁ N₀ ε' i
    · simp only [hF, if_pos hRi]; exact hblock i hi hRi j
    · simp only [hF, if_neg hRi]
      have hempty : L12cS Qn T K ε s₀ ε' i = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro r hr
        have hr' := Finset.mem_filter.mp hr
        have h1 : (1 : ℝ) ≤ r := by exact_mod_cast (Finset.mem_Icc.mp hr'.1).1
        exact hRi (h1.trans hr'.2.1)
      rw [hempty, Finset.sum_empty])
  refine hfam.trans ?_
  have hZ0 : 0 ≤ Z := by
    rw [hZ]; unfold Zsize; positivity
  have hblk : ∀ i ∈ Finset.range (⌈1 / ε'⌉₊ + 1),
      ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (F i j) ≤ ENNReal.ofReal (9 * C * Z ^ a) := by
    intro i _
    by_cases hRi : 1 ≤ Rblk R₁ N₀ ε' i
    · have hH0 : 0 ≤ Hblk T K N₀ Qn R₁ ε' i := by
        have := Z6c_Hge T K N₀ Qn R₁ ε' hK hQ hN0' hR1 i; linarith
      have hRH : Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i ≤ Z := by
        have := Z6c_rect T K N₀ Qn R₁ ε' hT hK hQ hN0' hR1 hε' i 1 hRi zero_le_one one_le_two
        rwa [Real.rpow_one] at this
      have hX0 : 0 ≤ Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i := by positivity
      have hFj : ∀ j : ℕ, F i j = C * (Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i) ^ a * ((2 : ℝ) ^ j) ^ a := by
        intro j
        simp only [hF, if_pos hRi]
        rw [show Rblk R₁ N₀ ε' i ^ 2 * (2 ^ j * Hblk T K N₀ Qn R₁ ε' i)
            = (Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i) * 2 ^ j by ring,
          Real.mul_rpow hX0 (by positivity)]
        ring
      have hc0 : 0 ≤ C * (Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i) ^ a := by positivity
      calc ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (F i j)
          = ENNReal.ofReal (C * (Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i) ^ a) *
              ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ a) := by
            rw [← ENNReal.tsum_mul_left]
            apply tsum_congr; intro j
            rw [hFj j, ENNReal.ofReal_mul hc0]; ring
        _ ≤ ENNReal.ofReal (C * (Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i) ^ a) * ENNReal.ofReal 9 := by
            gcongr; exact L12c_wsum k hk a ha0 ha2
        _ = ENNReal.ofReal (9 * C * (Rblk R₁ N₀ ε' i ^ 2 * Hblk T K N₀ Qn R₁ ε' i) ^ a) := by
            rw [← ENNReal.ofReal_mul hc0]; ring_nf
        _ ≤ ENNReal.ofReal (9 * C * Z ^ a) := by
            apply ENNReal.ofReal_le_ofReal
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow hX0 hRH ha0
    · have : ∀ j, F i j = 0 := fun j => by simp only [hF, if_neg hRi]
      simp only [this, ENNReal.ofReal_zero, mul_zero, tsum_zero]
      exact zero_le
  calc ∑ i ∈ Finset.range (⌈1 / ε'⌉₊ + 1), ∑' j : ℕ, ENNReal.ofReal (L12cw k j) * ENNReal.ofReal (F i j)
      ≤ ∑ i ∈ Finset.range (⌈1 / ε'⌉₊ + 1), ENNReal.ofReal (9 * C * Z ^ a) := Finset.sum_le_sum hblk
    _ = ENNReal.ofReal ((⌈1 / ε'⌉₊ + 1) * (9 * C * Z ^ a)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          show ((⌈1 / ε'⌉₊ : ℝ) + 1) = ((⌈1 / ε'⌉₊ + 1 : ℕ) : ℝ) by push_cast; ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end ShellS
end ZetaShell

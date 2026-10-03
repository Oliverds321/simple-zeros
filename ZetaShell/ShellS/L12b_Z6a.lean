/-
L7_12c (3 Oct 2026): node Z6a (L7_10's `L10_Z6a`, statement byte-identical): **Lemma 6a, zero sums, corrected form
(one `log N₀`)** (lem:shell-6a, sec_shell.tex l.649–664).
Proof: per character `L12b_char_tsum` (from `L12b_char_finite`, `L12b_rest_finite`), then the family sum:
`r/φ(r) ≤ C log s₀` (`L12b_rphi`, `r ≤ R₁ ≤ N₀`), `Σ_χ 𝒩_χ² ≤ (Σ_χ 𝒩_χ)²`, and the tall-zero terms
`Σ_{r≤R₁} (r/φ(r)) #{χ prim mod r} · O(e^{−4s₀}) ≤ R₁² O(e^{−4s₀}) ≤ O(e^{−s₀})` (`#prim(r) ≤ φ(r)`).
-/
import ZetaShell.ShellS.L10_Defs
import ZetaShell.ShellS.L12b_Char
import ZetaShell.ShellS.L12b_RPhi

noncomputable section
open Complex

namespace ZetaShell
namespace ShellS

open ZetaShell.PropZ

/-- **per-character Lemma 6a** (tsum form, with summability of the near and rest series). -/
theorem L12b_char_tsum {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (A₀ : ℝ)
    (hA₀ : 1 ≤ A₀)
    (hloc : ∀ (t : ℝ) (s : Finset {ρ : ℂ // IsNtZero χ ρ}), (∀ ρ ∈ s, t < ρ.1.im ∧ ρ.1.im ≤ t + 1) →
      ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) ≤ A₀ * (Real.log r + Real.log (|t| + 3)))
    (A k : ℕ) (hA : 2 ≤ A) (hk : 3 ≤ k) (T μ s₀ X₀ : ℝ) (hT : 2 ≤ T) (hTN : T ≤ Real.exp s₀) (hμ : 0 ≤ μ)
    (hμN : μ ≤ Real.exp s₀) (hs : 3 ≤ s₀) (hr : Real.log r ≤ s₀) :
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1) ∧
    Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1) ∧
    ∑' p, ShellS.pairTerm χ T μ s₀ A k p
      ≤ (1 + 2 * L12bcW) * (∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1) ^ 2
        + (1 + L12bcW) * (18 * A₀ * s₀ * ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1
          + 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀)) := by
  -- summability of m ϖ (as in `PropZ.Z5Z_summable`)
  set C₁ := 5 / 4 * (1 + 2 * T) ^ 2 * (μ + 1) ^ 2 with hC₁
  have hϖ : Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1) := by
    refine Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (varpi_nonneg0 T μ k ρ.1 hμ))
      (fun ρ => ?_) ((zero_sum_inv_sq r χ hχ).mul_left C₁)
    have h := varpi_le_inv_sq T μ k (by omega) (by linarith) hμ ρ.1 ⟨ρ.2.2.1, ρ.2.2.2⟩
    have hm : (0 : ℝ) ≤ zmult χ ρ.1 := Nat.cast_nonneg _
    calc (zmult χ ρ.1 : ℝ) * varpi T μ k ρ.1
        ≤ (zmult χ ρ.1 : ℝ) * (C₁ / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := mul_le_mul_of_nonneg_left h hm
      _ = C₁ * ((zmult χ ρ.1 : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ.1))) := by ring
  have hs0 : 0 ≤ s₀ := by linarith
  have hN : Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1) :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (L12b_gNear_nonneg T s₀ k X₀ μ ρ.1 hμ))
      (fun ρ => mul_le_mul_of_nonneg_left (L12b_gNear_le T s₀ k X₀ μ ρ.1 hμ hs0 ρ.2.2.2.le) (Nat.cast_nonneg _))
      hϖ
  have hR : Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1) :=
    Summable.of_nonneg_of_le (fun ρ => mul_nonneg (Nat.cast_nonneg _) (L12b_gRest_nonneg T s₀ k X₀ μ ρ.1))
      (fun ρ => mul_le_mul_of_nonneg_left (L12b_gRest_le T s₀ k X₀ μ ρ.1 hμ hs0 ρ.2.2.2.le) (Nat.cast_nonneg _))
      hϖ
  refine ⟨hN, hR, ?_⟩
  have hP : Summable (ShellS.pairTerm χ T μ s₀ A k) :=
    (Z5Z_summable A k (by omega) s₀ T μ hs0 hT hμ r χ hχ).congr (fun p => rfl)
  have hP0 : ∀ p, 0 ≤ ShellS.pairTerm χ T μ s₀ A k p := fun p => pairTerm_nonneg0 χ T μ s₀ A k hμ p
  apply hP.tsum_le_of_sum_le
  intro u
  classical
  set s := u.image Prod.fst ∪ u.image Prod.snd with hsdef
  have hus : u ⊆ s ×ˢ s := by
    intro p hp
    rw [Finset.mem_product]
    exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp),
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
  have hNs0 : 0 ≤ ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1 :=
    Finset.sum_nonneg fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (L12b_gNear_nonneg T s₀ k X₀ μ ρ.1 hμ)
  have hNs : ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1
      ≤ ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1 :=
    hN.sum_le_tsum s (fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (L12b_gNear_nonneg T s₀ k X₀ μ ρ.1 hμ))
  have hRs : ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1
      ≤ ∑' ρ : {ρ : ℂ // IsNtZero χ ρ}, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1 :=
    hR.sum_le_tsum s (fun ρ _ => mul_nonneg (Nat.cast_nonneg _) (L12b_gRest_nonneg T s₀ k X₀ μ ρ.1))
  have hcW := L12bcW_nonneg
  have hfin := L12b_char_finite χ A₀ hA₀ hloc A k hA T μ s₀ X₀ hμ s
  have hrest := L12b_rest_finite χ A₀ hA₀ hloc k hk T μ s₀ X₀ hT hTN hμ hμN hs hr s
  calc ∑ p ∈ u, ShellS.pairTerm χ T μ s₀ A k p
      ≤ ∑ p ∈ s ×ˢ s, ShellS.pairTerm χ T μ s₀ A k p :=
        Finset.sum_le_sum_of_subset_of_nonneg hus (fun p _ _ => hP0 p)
    _ = ∑ ρ ∈ s, ∑ ρ' ∈ s, ShellS.pairTerm χ T μ s₀ A k (ρ, ρ') := Finset.sum_product _ _ _
    _ ≤ (1 + 2 * L12bcW) * (∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ μ ρ.1) ^ 2
        + (1 + L12bcW) * (18 * A₀ * s₀ * ∑ ρ ∈ s, (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ μ ρ.1
          + 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀)) := by
        refine hfin.trans ?_
        have h1 : (0 : ℝ) ≤ 1 + L12bcW := by linarith
        linarith [mul_le_mul_of_nonneg_left hrest h1]
    _ ≤ _ := by
        have h1 : (0 : ℝ) ≤ 1 + L12bcW := by linarith
        have h2 : (0 : ℝ) ≤ 1 + 2 * L12bcW := by linarith
        have h3 : (0 : ℝ) ≤ 18 * A₀ * s₀ := by positivity
        have hsq := pow_le_pow_left₀ hNs0 hNs 2
        have := mul_le_mul_of_nonneg_left hsq h2
        have := mul_le_mul_of_nonneg_left hRs h3
        have := mul_le_mul_of_nonneg_left (add_le_add_right this (2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀))) h1
        linarith

/-- `#{χ primitive mod r} ≤ φ(r)`. -/
lemma L12b_card_prim (r : ℕ) [NeZero r] : ((primChars r).card : ℝ) ≤ (Nat.totient r : ℝ) := by
  have : NeZero ((Monoid.exponent (ZMod r)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩
  have h := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
  have h2 : (primChars r).card ≤ r.totient :=
    calc (primChars r).card ≤ Fintype.card (DirichletCharacter ℂ r) := Finset.card_le_univ _
      _ = Nat.card (DirichletCharacter ℂ r) := (Nat.card_eq_fintype_card).symm
      _ = r.totient := h
  exact_mod_cast h2

/-- `Σ_a Σ_b x² ≤ (Σ_a Σ_b x)²` for `x ≥ 0`. -/
lemma L12b_sumsq {α : Type*} {β : α → Type*} (s : Finset α) (t : ∀ a, Finset (β a)) (x : ∀ a, β a → ℝ)
    (hx : ∀ a ∈ s, ∀ b ∈ t a, 0 ≤ x a b) :
    ∑ a ∈ s, ∑ b ∈ t a, x a b ^ 2 ≤ (∑ a ∈ s, ∑ b ∈ t a, x a b) ^ 2 := by
  set S := ∑ a ∈ s, ∑ b ∈ t a, x a b with hS
  have hle : ∀ a ∈ s, ∀ b ∈ t a, x a b ≤ S := by
    intro a ha b hb
    calc x a b ≤ ∑ b' ∈ t a, x a b' := Finset.single_le_sum (fun b' hb' => hx a ha b' hb') hb
      _ ≤ S := Finset.single_le_sum (f := fun a => ∑ b ∈ t a, x a b)
          (fun a' ha' => Finset.sum_nonneg fun b' hb' => hx a' ha' b' hb') ha
  calc ∑ a ∈ s, ∑ b ∈ t a, x a b ^ 2 ≤ ∑ a ∈ s, ∑ b ∈ t a, x a b * S := by
        apply Finset.sum_le_sum; intro a ha; apply Finset.sum_le_sum; intro b hb
        rw [sq]; exact mul_le_mul_of_nonneg_left (hle a ha b hb) (hx a ha b hb)
    _ = S ^ 2 := by
        rw [sq, hS, Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul]

theorem Z6a_zero_sums (A k : ℕ) (hA : 2 ≤ A) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Qn : ℕ) (T K ε s₀ X₀ : ℝ), 3 ≤ (Qn : ℝ) → 2 ≤ T → T ≤ Real.exp s₀ → 1 ≤ K →
      K ≤ (Qn : ℝ) → 3 ≤ s₀ → (R1S Qn ε s₀ : ℝ) ≤ Real.exp s₀ → 0 ≤ X₀ →
      famZeroSummable Qn K ε s₀ (gNear T s₀ k X₀) ∧ famZeroSummable Qn K ε s₀ (gRest T s₀ k X₀) ∧
      zeroPairSum Qn T K ε s₀ A k
        ≤ C * Real.log s₀ * (nearSum Qn T K ε s₀ k X₀ ^ 2 + s₀ * restSq Qn T K ε s₀ k X₀)
          + C / Real.exp s₀ := by
  obtain ⟨A₀, hA₀, hloc⟩ := L12b_local_count
  obtain ⟨Cφ, hCφ, hrphi⟩ := L12b_rphi
  have hcW := L12bcW_nonneg
  set c1 := Cφ * (1 + 2 * L12bcW) with hc1
  set c2 := Cφ * (1 + L12bcW) * (18 * A₀) with hc2
  set c3 := (1 + L12bcW) * (2048 * A₀ ^ 2 * L12bcW) with hc3
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by have : (0 : ℝ) ≤ A₀ := by linarith
                           positivity
  have hc30 : 0 ≤ c3 := by positivity
  refine ⟨max (max c1 c2) c3, le_trans hc10 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro Qn T K ε s₀ X₀ hQ hT hTN hK1 hKQ hs hR1 hX₀
  set N₀ := Real.exp s₀ with hN₀
  set R₁ := R1S Qn ε s₀ with hR₁def
  have hN₀pos : 0 < N₀ := Real.exp_pos s₀
  have hQpos : (0 : ℝ) < Qn := by linarith
  -- the per-(r, χ) facts
  have hrange : ∀ r ∈ Finset.Icc 1 R₁, (1 ≤ r) ∧ (r : ℝ) ≤ N₀ ∧ Real.log r ≤ s₀ ∧
      0 ≤ muR Qn K s₀ r ∧ muR Qn K s₀ r ≤ N₀ := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr.1
    have hrR : (r : ℝ) ≤ R₁ := by exact_mod_cast hr.2
    have hrN : (r : ℝ) ≤ N₀ := hrR.trans hR1
    refine ⟨hr.1, hrN, ?_, ?_, ?_⟩
    · have := Real.log_le_log (by linarith) hrN; rwa [hN₀, Real.log_exp] at this
    · unfold muR; positivity
    · unfold muR
      rw [div_le_iff₀ (by positivity)]
      have : K ≤ (r : ℝ) * Qn := le_trans hKQ (le_mul_of_one_le_left hQpos.le hr1)
      calc K * Real.exp s₀ ≤ ((r : ℝ) * Qn) * Real.exp s₀ := mul_le_mul_of_nonneg_right this hN₀pos.le
        _ = Real.exp s₀ * (r * Qn) := by ring
  have hprim : ∀ r, ∀ χ ∈ primChars r, χ.IsPrimitive := by
    intro r χ hχ
    classical
    simp only [primChars, Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    exact hχ
  have hchar : ∀ r ∈ Finset.Icc 1 R₁, ∀ χ ∈ primChars r, ∀ h : r ≠ 0,
      haveI : NeZero r := ⟨h⟩;
      Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ (muR Qn K s₀ r) ρ.1) ∧
      Summable (fun ρ : {ρ : ℂ // IsNtZero χ ρ} => (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ (muR Qn K s₀ r) ρ.1) ∧
      ∑' p, ShellS.pairTerm χ T (muR Qn K s₀ r) s₀ A k p
        ≤ (1 + 2 * L12bcW) * (∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
            (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ (muR Qn K s₀ r) ρ.1) ^ 2
          + (1 + L12bcW) * (18 * A₀ * s₀ * ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
            (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ (muR Qn K s₀ r) ρ.1
            + 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀)) := by
    intro r hr χ hχ h
    have : NeZero r := ⟨h⟩
    obtain ⟨_, _, hlogr, hμ0, hμN⟩ := hrange r hr
    exact L12b_char_tsum χ (hprim r χ hχ) A₀ hA₀ (hloc r χ (hprim r χ hχ)) A k hA hk T _ s₀ X₀ hT hTN hμ0 hμN
      hs hlogr
  refine ⟨fun r hr χ hχ h => (hchar r hr χ hχ h).1, fun r hr χ hχ h => (hchar r hr χ hχ h).2.1, ?_⟩
  -- notation for the per-(r,χ) sums
  set Pz : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r χ => if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩; ∑' p, ShellS.pairTerm χ T (muR Qn K s₀ r) s₀ A k p with hPzdef
  set Nz : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r χ => if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩; ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
      (zmult χ ρ.1 : ℝ) * gNear T s₀ k X₀ (muR Qn K s₀ r) ρ.1 with hNzdef
  set Rz : (r : ℕ) → DirichletCharacter ℂ r → ℝ := fun r χ => if h : r = 0 then 0 else
    haveI : NeZero r := ⟨h⟩; ∑' ρ : {ρ : ℂ // IsNtZero χ ρ},
      (zmult χ ρ.1 : ℝ) * gRest T s₀ k X₀ (muR Qn K s₀ r) ρ.1 with hRzdef
  set τ := 2048 * A₀ ^ 2 * L12bcW / Real.exp (4 * s₀) with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hZ : zeroPairSum Qn T K ε s₀ A k = ∑ r ∈ Finset.Icc 1 R₁, ((r : ℝ) / (Nat.totient r : ℝ)) *
      ∑ χ ∈ primChars r, Pz r χ := rfl
  have hNS : nearSum Qn T K ε s₀ k X₀ = ∑ r ∈ Finset.Icc 1 R₁, ∑ χ ∈ primChars r, Nz r χ := rfl
  have hRS : restSq Qn T K ε s₀ k X₀ = ∑ r ∈ Finset.Icc 1 R₁, ∑ χ ∈ primChars r, Rz r χ := rfl
  have hNz0 : ∀ r ∈ Finset.Icc 1 R₁, ∀ χ ∈ primChars r, 0 ≤ Nz r χ := by
    intro r _ χ _
    simp only [hNzdef]
    split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (L12b_gNear_nonneg _ _ _ _ _ _
        (by unfold muR; positivity))
  have hRz0 : ∀ r ∈ Finset.Icc 1 R₁, ∀ χ ∈ primChars r, 0 ≤ Rz r χ := by
    intro r _ χ _
    simp only [hRzdef]
    split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun ρ => mul_nonneg (Nat.cast_nonneg _) (L12b_gRest_nonneg _ _ _ _ _ _)
  have hPz : ∀ r ∈ Finset.Icc 1 R₁, ∀ χ ∈ primChars r,
      Pz r χ ≤ (1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀ * Rz r χ + τ) := by
    intro r hr χ hχ
    have h0 : r ≠ 0 := by have := (hrange r hr).1; omega
    have := (hchar r hr χ hχ h0).2.2
    simp only [hPzdef, hNzdef, hRzdef, dif_neg h0]
    exact this
  have hlogs : 0 ≤ Real.log s₀ := Real.log_nonneg (by linarith)
  have hrφ : ∀ r ∈ Finset.Icc 1 R₁, 0 ≤ (r : ℝ) / (Nat.totient r : ℝ) ∧
      (r : ℝ) / (Nat.totient r : ℝ) ≤ Cφ * Real.log s₀ := by
    intro r hr
    obtain ⟨h1, h2, _, _, _⟩ := hrange r hr
    exact ⟨by positivity, hrphi r s₀ h1 hs h2⟩
  -- the main bound
  set NS := nearSum Qn T K ε s₀ k X₀ with hNSdef
  set RS := restSq Qn T K ε s₀ k X₀ with hRSdef
  have hsumsq : ∑ r ∈ Finset.Icc 1 R₁, ∑ χ ∈ primChars r, Nz r χ ^ 2 ≤ NS ^ 2 := by
    rw [hNS]; exact L12b_sumsq _ _ _ hNz0
  have hRS0 : 0 ≤ RS := by rw [hRS]; exact Finset.sum_nonneg fun r hr => Finset.sum_nonneg fun χ hχ => hRz0 r hr χ hχ
  have hstep1 : zeroPairSum Qn T K ε s₀ A k
      ≤ ∑ r ∈ Finset.Icc 1 R₁, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r,
          ((1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * Rz r χ)
        + ∑ r ∈ Finset.Icc 1 R₁, ((r : ℝ) / (Nat.totient r : ℝ)) * (((primChars r).card : ℝ) * ((1 + L12bcW) * τ)) := by
    rw [hZ, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro r hr
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (hrφ r hr).1
    calc ∑ χ ∈ primChars r, Pz r χ
        ≤ ∑ χ ∈ primChars r, (((1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * Rz r χ)
            + (1 + L12bcW) * τ) := by
          apply Finset.sum_le_sum; intro χ hχ
          have := hPz r hr χ hχ
          linarith
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hstep2 : ∑ r ∈ Finset.Icc 1 R₁, ((r : ℝ) / (Nat.totient r : ℝ)) * ∑ χ ∈ primChars r,
          ((1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * Rz r χ)
      ≤ Cφ * Real.log s₀ * ((1 + 2 * L12bcW) * NS ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * RS) := by
    have hin : ∀ r ∈ Finset.Icc 1 R₁, 0 ≤ ∑ χ ∈ primChars r,
        ((1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * Rz r χ) := by
      intro r hr
      apply Finset.sum_nonneg; intro χ hχ
      have := hRz0 r hr χ hχ
      have : (0 : ℝ) ≤ A₀ := by linarith
      have : (0 : ℝ) ≤ s₀ := by linarith
      positivity
    have e : ∑ r ∈ Finset.Icc 1 R₁, ∑ χ ∈ primChars r,
          ((1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * Rz r χ)
        = (1 + 2 * L12bcW) * ∑ r ∈ Finset.Icc 1 R₁, ∑ χ ∈ primChars r, Nz r χ ^ 2
            + (1 + L12bcW) * (18 * A₀ * s₀) * RS := by
      rw [hRS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro r _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ r ∈ Finset.Icc 1 R₁, Cφ * Real.log s₀ * ∑ χ ∈ primChars r,
          ((1 + 2 * L12bcW) * Nz r χ ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * Rz r χ) :=
          Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_right (hrφ r hr).2 (hin r hr)
      _ = Cφ * Real.log s₀ * ((1 + 2 * L12bcW) * ∑ r ∈ Finset.Icc 1 R₁, ∑ χ ∈ primChars r, Nz r χ ^ 2
            + (1 + L12bcW) * (18 * A₀ * s₀) * RS) := by
          rw [← Finset.mul_sum, e]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h2 : (0 : ℝ) ≤ 1 + 2 * L12bcW := by linarith
          linarith [mul_le_mul_of_nonneg_left hsumsq h2]
  have hstep3 : ∑ r ∈ Finset.Icc 1 R₁, ((r : ℝ) / (Nat.totient r : ℝ)) * (((primChars r).card : ℝ) * ((1 + L12bcW) * τ))
      ≤ c3 / N₀ := by
    have hpt : ∀ r ∈ Finset.Icc 1 R₁, ((r : ℝ) / (Nat.totient r : ℝ)) * (((primChars r).card : ℝ) * ((1 + L12bcW) * τ))
        ≤ (R₁ : ℝ) * ((1 + L12bcW) * τ) := by
      intro r hr
      obtain ⟨h1, _, _, _, _⟩ := hrange r hr
      have : NeZero r := ⟨by omega⟩
      have hφpos : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr (by omega)
      have hcard := L12b_card_prim r
      have hrR : (r : ℝ) ≤ R₁ := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      have h0 : 0 ≤ (1 + L12bcW) * τ := by positivity
      calc ((r : ℝ) / (Nat.totient r : ℝ)) * (((primChars r).card : ℝ) * ((1 + L12bcW) * τ))
          = (r : ℝ) * (((primChars r).card : ℝ) / (Nat.totient r : ℝ)) * ((1 + L12bcW) * τ) := by ring
        _ ≤ (r : ℝ) * 1 * ((1 + L12bcW) * τ) := by
            apply mul_le_mul_of_nonneg_right _ h0
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            rw [div_le_one hφpos]; exact hcard
        _ ≤ (R₁ : ℝ) * ((1 + L12bcW) * τ) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hrR h0
    calc _ ≤ ∑ r ∈ Finset.Icc 1 R₁, (R₁ : ℝ) * ((1 + L12bcW) * τ) := Finset.sum_le_sum hpt
      _ = (R₁ : ℝ) * ((R₁ : ℝ) * ((1 + L12bcW) * τ)) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ ≤ N₀ * (N₀ * ((1 + L12bcW) * τ)) := by
          have h0 : 0 ≤ (1 + L12bcW) * τ := by positivity
          have hR0 : (0 : ℝ) ≤ R₁ := Nat.cast_nonneg _
          apply mul_le_mul hR1 (mul_le_mul_of_nonneg_right hR1 h0) (by positivity) hN₀pos.le
      _ = c3 / N₀ * (N₀ ^ 3 / Real.exp (4 * s₀)) := by
          rw [hτ, hc3]
          have hNe : N₀ ≠ 0 := hN₀pos.ne'
          field_simp
      _ ≤ c3 / N₀ * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (Real.exp_pos _), hN₀, ← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr; push_cast; linarith
      _ = c3 / N₀ := mul_one _
  -- conclude
  have hC1 : c1 ≤ max (max c1 c2) c3 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : c2 ≤ max (max c1 c2) c3 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC3 : c3 ≤ max (max c1 c2) c3 := le_max_right _ _
  set C := max (max c1 c2) c3 with hC
  have hfin1 : Cφ * Real.log s₀ * ((1 + 2 * L12bcW) * NS ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * RS)
      ≤ C * Real.log s₀ * (NS ^ 2 + s₀ * RS) := by
    have e : Cφ * Real.log s₀ * ((1 + 2 * L12bcW) * NS ^ 2 + (1 + L12bcW) * (18 * A₀ * s₀) * RS)
        = Real.log s₀ * (c1 * NS ^ 2 + c2 * (s₀ * RS)) := by rw [hc1, hc2]; ring
    rw [e]
    have hs0 : 0 ≤ s₀ * RS := mul_nonneg (by linarith) hRS0
    have hN2 : 0 ≤ NS ^ 2 := sq_nonneg _
    have : c1 * NS ^ 2 + c2 * (s₀ * RS) ≤ C * (NS ^ 2 + s₀ * RS) := by
      nlinarith [mul_le_mul_of_nonneg_right hC1 hN2, mul_le_mul_of_nonneg_right hC2 hs0]
    calc Real.log s₀ * (c1 * NS ^ 2 + c2 * (s₀ * RS)) ≤ Real.log s₀ * (C * (NS ^ 2 + s₀ * RS)) :=
          mul_le_mul_of_nonneg_left this hlogs
      _ = C * Real.log s₀ * (NS ^ 2 + s₀ * RS) := by ring
  have hfin3 : c3 / N₀ ≤ C / Real.exp s₀ := div_le_div_of_nonneg_right hC3 hN₀pos.le
  linarith [hstep1, hstep2, hstep3, hfin1, hfin3]

end ShellS
end ZetaShell

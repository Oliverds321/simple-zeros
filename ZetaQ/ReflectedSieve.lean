/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
ZetaQ/ReflectedSieve.lean — the REFLECTED large sieve for a parity class (Corollary 3″ input).

Imports `ZetaQ.Gallagher` (the sorry-free Gallagher sieve) and `ZetaQ.Certificate` (for
`Family`). Parameter-free: no `ParamsQ`, `T`, `λ`, `X`.

--------------------------------------------------------------------------------------
## What this file proves
--------------------------------------------------------------------------------------

For a parity class `p` (`parity χ = 0`: even, `= 1`: odd) and any `a : ℕ → ℂ`,

    Σ_{q≤Q} Σ*_{χ mod q, parity χ = p} |Σ_{n≤N} a_n χ(n)|²  ≤  (Q²/2 + π(N + ½)) Σ_{n≤N} |a_n|²

(`reflected_large_sieve_gallagher`), and the same bound for each of Corollary 3's four parity
`Family`s (`reflected_large_sieve_parityFamily`). Each parity class is charged `Q²/2` — its
exact share of the `Q²` that is the family constant times `|𝔉_Q|` — so, against
`|𝔉^±_Q| = ½|𝔉_Q| + O(Q)`, the out-zone constant of the parity families is the FULL-family
constant `C` (`π⁴/18` for `q ≤ Q`, `2π⁴/27` dyadic), not the `2C` (`CfamEven`,
`CfamEvenDyadic`) that bounding a parity class by the whole family costs.

Mathematics: the reflection trick (H4 §2.3; audited as V1 §1): with `ε = (−1)^p`, the sequence
`c_n = ½a_n`, `c_{−n} = ½εa_n` on `[−N, N]` has `Σ c_mχ(m) = ½(1 + εχ(−1))F_χ`, which is `F_χ` on
the class and `0` off it, and `‖c‖² = ½‖a‖²`; the additive sieve on an interval of `2N + 1`
integers gives `(Q² + π(2N+1))·½‖a‖²`. Lean realises `[−N, N]` inside `ℕ` by translating by
`K = (Q + N + 1)!`, which every modulus `q ≤ Q` divides (so `χ(K ± n) = χ(±n)`), and uses the
WINDOWED Gallagher sieve `multiplicative_large_sieve_gallagher_window` (length term = window
length, via `ZetaQ.Gallagher.gallagher_shifted`). No new Gauss-sum work is needed:
`primitive_decomposition` is applied unchanged.

Rule 17: CLEAN — `N` and `Q` independent, no parameters.
-/
import ZetaQ.Gallagher
import ZetaQ.Certificate

noncomputable section

open scoped BigOperators

namespace ZetaQ
namespace Reflected

open ZetaQ.Gallagher

/-! ## 1. The multiplicative sieve for a coefficient vector supported on a WINDOW -/

/-- A sum over `Ioc 0 (M + L)` of a function vanishing on `Ioc 0 M` is the sum over the window
`Ioc M (M + L)`. -/
theorem sum_Ioc_window {β : Type*} [AddCommMonoid β] (M L : ℕ) (f : ℕ → β)
    (hf : ∀ n ∈ Finset.Ioc 0 M, f n = 0) :
    ∑ n ∈ Finset.Ioc 0 (M + L), f n = ∑ n ∈ Finset.Ioc M (M + L), f n := by
  rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le M) (Nat.le_add_right M L),
    Finset.sum_eq_zero hf, zero_add]

/-- **Lemma 6.1 at the Gallagher budget, windowed.** If `a` vanishes on `(0, M]`, then
`Σ_{q≤Q}Σ*_χ |Σ_{n≤M+L} a_n χ(n)|² ≤ (Q² + πL)·Σ_{M<n≤M+L}|a_n|²` — the length term is the
window length `L`, not `M + L`. Same Farey/Gauss deduction as
`multiplicative_large_sieve_gallagher`, with `gallagher_shifted` as the additive engine. -/
theorem multiplicative_large_sieve_gallagher_window (Q M L : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Finset.Ioc 0 M, a n = 0) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q (M + L) a χ‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + Real.pi * L) * ∑ n ∈ Finset.Ioc M (M + L), ‖a n‖ ^ 2 := by
  classical
  have hl2 : (0:ℝ) ≤ ∑ n ∈ Finset.Ioc M (M + L), ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hwin : ∀ θ : ℝ, expSum (M + L) a θ = ∑ n ∈ Finset.Ioc M (M + L), a n * e ((n : ℝ) * θ) :=
    fun θ => sum_Ioc_window M L _ (fun n hn => by rw [ha n hn, zero_mul])
  rcases Nat.eq_zero_or_pos Q with rfl | hQ1
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    refine mul_nonneg ?_ hl2
    positivity
  · have hQR : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQ1
    set T : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 Q).sigma reducedResidues with hT
    have hδ : (0:ℝ) < ((Q:ℝ) ^ 2)⁻¹ := by positivity
    have hsep : ∀ i j : {x // x ∈ T}, i ≠ j → ∀ m : ℤ,
        ((Q:ℝ) ^ 2)⁻¹
          ≤ |((i.1.2 : ℝ) / (i.1.1 : ℝ)) - ((j.1.2 : ℝ) / (j.1.1 : ℝ)) - (m : ℝ)| := by
      rintro ⟨⟨q, b⟩, hi⟩ ⟨⟨q', b'⟩, hj⟩ hij m
      have hi' := hi
      have hj' := hj
      rw [hT, Finset.mem_sigma, Finset.mem_Icc, mem_reducedResidues] at hi' hj'
      refine farey_spaced Q hi'.1.1 hj'.1.1 hi'.1.2 hj'.1.2 hi'.2.2 hj'.2.2 ?_ m
      rw [Nat.mod_eq_of_lt hi'.2.1, Nat.mod_eq_of_lt hj'.2.1]
      intro hcontra
      simp only [Prod.mk.injEq] at hcontra
      obtain ⟨rfl, rfl⟩ := hcontra
      exact hij rfl
    have hδ1 : ((Q:ℝ) ^ 2)⁻¹ ≤ 1 := by
      have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ1
      rw [inv_le_one_iff₀]
      right; nlinarith
    have hmain := gallagher_shifted (ι := {x // x ∈ T}) M L a
      (fun x => (x.1.2 : ℝ) / (x.1.1 : ℝ)) hδ hδ1 hsep
    rw [inv_inv] at hmain
    have hsumeq : ∑ i : {x // x ∈ T}, ‖expSum (M + L) a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2
        = ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ reducedResidues q,
            ‖expSum (M + L) a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
      rw [Finset.sum_coe_sort T
        (fun x => ‖expSum (M + L) a ((x.2 : ℝ) / (x.1 : ℝ))‖ ^ 2), hT]
      exact Finset.sum_sigma _ _ _
    have hmain' : ∑ i : {x // x ∈ T}, ‖expSum (M + L) a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2
        ≤ ((Q : ℝ) ^ 2 + Real.pi * L) * ∑ n ∈ Finset.Ioc M (M + L), ‖a n‖ ^ 2 := by
      simp only [hwin]
      exact hmain
    calc ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q (M + L) a χ‖ ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ reducedResidues q,
            ‖expSum (M + L) a ((b : ℝ) / (q : ℝ))‖ ^ 2 := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.mem_Icc] at hq
          refine (primitive_decomposition q (M + L) hq.1 a).trans ?_
          have h1 : (Nat.totient q : ℝ) / (q : ℝ) ≤ 1 := by
            rw [div_le_one (by exact_mod_cast hq.1)]
            exact_mod_cast Nat.totient_le q
          have h2 : (0:ℝ) ≤ ∑ b ∈ reducedResidues q,
              ‖expSum (M + L) a ((b : ℝ) / (q : ℝ))‖ ^ 2 :=
            Finset.sum_nonneg fun _ _ => by positivity
          nlinarith
      _ = ∑ i : {x // x ∈ T}, ‖expSum (M + L) a ((i.1.2 : ℝ) / (i.1.1 : ℝ))‖ ^ 2 :=
          hsumeq.symm
      _ ≤ ((Q : ℝ) ^ 2 + Real.pi * L) * ∑ n ∈ Finset.Ioc M (M + L), ‖a n‖ ^ 2 := hmain'

/-! ## 2. Reindexing helpers -/

/-- Reflection: `Σ_{K−N ≤ k < K} g k = Σ_{0<n≤N} g (K − n)` (for `N ≤ K`). -/
theorem sum_Ico_reflect_window {β : Type*} [AddCommMonoid β] (K N : ℕ) (hNK : N ≤ K)
    (g : ℕ → β) :
    ∑ k ∈ Finset.Ico (K - N) K, g k = ∑ n ∈ Finset.Ioc 0 N, g (K - n) := by
  have h := Finset.sum_Ico_reflect g 1 (m := N + 1) (n := K) (by omega)
  rw [show K + 1 - (N + 1) = K - N by omega, show K + 1 - 1 = K by omega] at h
  rw [← h, ← Finset.Ico_add_one_add_one_eq_Ioc, zero_add]

/-- `χ(−1) = (−1)^{parity χ}`. -/
theorem char_neg_one_eq_pow_parity {q : ℕ} (χ : DirichletCharacter ℂ q) :
    χ (-1) = (-1 : ℂ) ^ parity χ := by
  classical
  unfold parity
  split_ifs with he
  · rw [pow_zero]; exact he
  · rcases χ.even_or_odd with h | h
    · exact absurd h he
    · rw [pow_one]; exact h

/-! ## 3. The reflected large sieve -/

/-- **The reflected large sieve at the Gallagher budget** (H4 §2.3, audited by V1 §1; here with
Gallagher's constant). For each parity class `p` (`0` = even, `1` = odd):

  `Σ_{q≤Q} Σ*_{χ, parity χ = p} |Σ_{n≤N} a_n χ(n)|² ≤ (Q²/2 + π(N + ½))·Σ_{n≤N}|a_n|²`.

Each parity class is charged `Q²/2` — its exact share of the `Q²` — which is what restores the
FULL-family constant `C = Q²/|𝔉_Q|` for Corollary 3's parity families (`Q²/2` against
`|𝔉^±_Q| = ½|𝔉_Q| + O(Q)`), instead of `2C`.

Proof: with `ε = (−1)^p` and `K = (Q + N + 1)!` (divisible by every `q ≤ Q`), put
`d_{K+n} = ½a_n`, `d_{K−n} = ½εa_n` (`1 ≤ n ≤ N`), zero elsewhere. For `q ∣ K`, `χ(K ± n) = χ(±n)`
and `χ(−n) = χ(−1)χ(n)`, so `Σ_k d_kχ(k) = ½(1 + εχ(−1))F_χ`, which is `F_χ` on the class `p`.
`d` lives on the window `(K−N−1, K+N]` of length `2N + 1`, with `‖d‖² = ½‖a‖²`; the windowed
Gallagher sieve gives `(Q² + π(2N+1))·½‖a‖²`. -/
theorem reflected_large_sieve_gallagher (Q N p : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
        ‖charSum q N a χ‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 / 2 + Real.pi * ((N : ℝ) + 1 / 2)) * l2sq N a := by
  classical
  set K : ℕ := (Q + N + 1).factorial with hKdef
  have hKN : N + 1 ≤ K := by
    have := Nat.self_le_factorial (Q + N + 1)
    omega
  have hdvd : ∀ q ∈ Finset.Icc 1 Q, q ∣ K := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    exact Nat.dvd_factorial (by omega) (by omega)
  set ε : ℂ := (-1 : ℂ) ^ p with hεdef
  have hε1 : ‖ε‖ = 1 := by rw [hεdef, norm_pow, norm_neg, norm_one, one_pow]
  set dp : ℕ → ℂ := fun k => if k ∈ Finset.Ioc K (K + N) then (1 / 2 : ℂ) * a (k - K) else 0
    with hdp
  set dm : ℕ → ℂ := fun k => if k ∈ Finset.Ico (K - N) K then (1 / 2 : ℂ) * ε * a (K - k) else 0
    with hdm
  set d : ℕ → ℂ := fun k => dp k + dm k with hd
  set M : ℕ := K - N - 1 with hM
  have hML : M + (2 * N + 1) = K + N := by omega
  -- `d` vanishes below the window
  have hd0 : ∀ n ∈ Finset.Ioc 0 M, d n = 0 := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have h1 : n ∉ Finset.Ioc K (K + N) := by rw [Finset.mem_Ioc]; omega
    have h2 : n ∉ Finset.Ico (K - N) K := by rw [Finset.mem_Ico]; omega
    simp only [hd, hdp, hdm, if_neg h1, if_neg h2, add_zero]
  have hsieve := multiplicative_large_sieve_gallagher_window Q M (2 * N + 1) d hd0
  rw [hML] at hsieve
  -- the window norm: `‖d‖² = ½‖a‖²`
  have hsubp : Finset.Ioc K (K + N) ⊆ Finset.Ioc M (K + N) := by
    intro k hk; rw [Finset.mem_Ioc] at hk ⊢; omega
  have hsubm : Finset.Ico (K - N) K ⊆ Finset.Ioc M (K + N) := by
    intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_Ioc]; omega
  have hpt : ∀ k, ‖d k‖ ^ 2
      = (if k ∈ Finset.Ioc K (K + N) then ‖(1 / 2 : ℂ) * a (k - K)‖ ^ 2 else 0)
        + (if k ∈ Finset.Ico (K - N) K then ‖(1 / 2 : ℂ) * ε * a (K - k)‖ ^ 2 else 0) := by
    intro k
    by_cases h1 : k ∈ Finset.Ioc K (K + N)
    · have h2 : k ∉ Finset.Ico (K - N) K := by
        rw [Finset.mem_Ioc] at h1; rw [Finset.mem_Ico]; omega
      simp only [hd, hdp, hdm, if_pos h1, if_neg h2, add_zero]
    · simp only [hd, hdp, hdm, if_neg h1, zero_add]
      split_ifs <;> simp
  have hnorm : ∑ k ∈ Finset.Ioc M (K + N), ‖d k‖ ^ 2 = (1 / 2 : ℝ) * l2sq N a := by
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.inter_eq_right.2 hsubp, Finset.inter_eq_right.2 hsubm]
    rw [sum_Ico_reflect_window K N (by omega), sum_Ioc_shift K N]
    have e1 : ∀ n ∈ Finset.Ioc 0 N, ‖(1 / 2 : ℂ) * a (K + n - K)‖ ^ 2 = (1 / 4) * ‖a n‖ ^ 2 := by
      intro n _
      rw [Nat.add_sub_cancel_left, norm_mul, mul_pow]
      norm_num
    have e2 : ∀ n ∈ Finset.Ioc 0 N,
        ‖(1 / 2 : ℂ) * ε * a (K - (K - n))‖ ^ 2 = (1 / 4) * ‖a n‖ ^ 2 := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Nat.sub_sub_self (by omega), norm_mul, norm_mul, hε1, mul_pow, mul_pow]
      norm_num
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, l2sq]
    ring
  -- the character-sum identity on the class `p`
  have hchar : ∀ q ∈ Finset.Icc 1 Q, ∀ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
      charSum q (K + N) d χ = charSum q N a χ := by
    intro q hq χ hχ
    rw [Finset.mem_filter] at hχ
    have hK0 : ((K : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff K q).2 (hdvd q hq)
    have hpar : ε * χ (-1) = 1 := by
      rw [char_neg_one_eq_pow_parity, hχ.2, hεdef, ← mul_pow]
      norm_num
    have hsplit : charSum q (K + N) d χ
        = ∑ k ∈ Finset.Ioc 0 (K + N), (if k ∈ Finset.Ioc K (K + N) then
              (1 / 2 : ℂ) * a (k - K) * χ (k : ZMod q) else 0)
          + ∑ k ∈ Finset.Ioc 0 (K + N), (if k ∈ Finset.Ico (K - N) K then
              (1 / 2 : ℂ) * ε * a (K - k) * χ (k : ZMod q) else 0) := by
      rw [charSum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hd, hdp, hdm, add_mul, ite_mul, zero_mul]
    have hsp : Finset.Ioc K (K + N) ⊆ Finset.Ioc 0 (K + N) := by
      intro k hk; rw [Finset.mem_Ioc] at hk ⊢; omega
    have hsm : Finset.Ico (K - N) K ⊆ Finset.Ioc 0 (K + N) := by
      intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_Ioc]; omega
    rw [hsplit, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsp,
      Finset.inter_eq_right.2 hsm, sum_Ico_reflect_window K N (by omega), sum_Ioc_shift K N]
    have e1 : ∀ n ∈ Finset.Ioc 0 N, (1 / 2 : ℂ) * a (K + n - K) * χ (((K + n : ℕ)) : ZMod q)
        = (1 / 2 : ℂ) * (a n * χ (n : ZMod q)) := by
      intro n _
      rw [Nat.add_sub_cancel_left, Nat.cast_add, hK0, zero_add]
      ring
    have e2 : ∀ n ∈ Finset.Ioc 0 N,
        (1 / 2 : ℂ) * ε * a (K - (K - n)) * χ (((K - n : ℕ)) : ZMod q)
          = (1 / 2 : ℂ) * (a n * χ (n : ZMod q)) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Nat.sub_sub_self (by omega), Nat.cast_sub (by omega), hK0, zero_sub,
        show (-(n : ZMod q)) = (-1) * (n : ZMod q) by ring, map_mul]
      have : (1 / 2 : ℂ) * ε * a n * (χ (-1) * χ (n : ZMod q))
          = (1 / 2 : ℂ) * (ε * χ (-1)) * (a n * χ (n : ZMod q)) := by ring
      rw [this, hpar]
      ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.mul_sum, charSum]
    ring
  -- assemble
  calc ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
        ‖charSum q N a χ‖ ^ 2
      = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ (primitiveChars q).filter (fun χ => parity χ = p),
          ‖charSum q (K + N) d χ‖ ^ 2 := by
        refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun χ hχ => ?_
        rw [hchar q hq χ hχ]
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ primitiveChars q, ‖charSum q (K + N) d χ‖ ^ 2 := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ ≤ ((Q : ℝ) ^ 2 + Real.pi * ((2 * N + 1 : ℕ) : ℝ))
          * ∑ k ∈ Finset.Ioc M (K + N), ‖d k‖ ^ 2 := hsieve
    _ = ((Q : ℝ) ^ 2 / 2 + Real.pi * ((N : ℝ) + 1 / 2)) * l2sq N a := by
        rw [hnorm]
        push_cast
        ring


/-! ## 4. Corollary 3's four parity families -/

/-- Every family's modulus range lies in `[1, Qn]`. -/
theorem Family.moduli_subset_Icc_one (F : Family) (Qn : ℕ) :
    F.moduli Qn ⊆ Finset.Icc 1 Qn := by
  intro q hq
  cases F <;> simp only [Family.moduli, Finset.mem_Icc, Finset.mem_Ioc] at hq ⊢ <;> omega

/-- **The reflected sieve for Corollary 3's parity families** (`evenQle`, `oddQle`,
`evenDyadic`, `oddDyadic`, i.e. `¬ F.IsFull`): the family's character sums obey the budget
`Qn²/2 + π(N + ½)`. For the dyadic families this keeps `Qn²/2` (drop `q ≤ Qn/2` by
positivity), which against `|𝔉^±_dy| = ½|𝔉_dy| + O(Q)` is again the full dyadic constant. -/
theorem reflected_large_sieve_parityFamily (F : Family) (hF : ¬ F.IsFull) (Qn N : ℕ)
    (a : ℕ → ℂ) :
    ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, ‖charSum q N a χ‖ ^ 2
      ≤ ((Qn : ℝ) ^ 2 / 2 + Real.pi * ((N : ℝ) + 1 / 2)) * l2sq N a := by
  classical
  have hsub := Family.moduli_subset_Icc_one F Qn
  have key : ∀ p : ℕ, (∀ q, F.chars q = (primitiveChars q).filter (fun χ => parity χ = p)) →
      ∑ q ∈ F.moduli Qn, ∑ χ ∈ F.chars q, ‖charSum q N a χ‖ ^ 2
        ≤ ((Qn : ℝ) ^ 2 / 2 + Real.pi * ((N : ℝ) + 1 / 2)) * l2sq N a := by
    intro p hp
    simp only [hp]
    refine le_trans ?_ (reflected_large_sieve_gallagher Qn N p a)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun q _ _ => Finset.sum_nonneg fun χ _ => by positivity)
  cases F with
  | qle => exact absurd Family.isFull_qle hF
  | dyadic => exact absurd Family.isFull_dyadic hF
  | evenQle => exact key 0 (fun q => rfl)
  | oddQle => exact key 1 (fun q => rfl)
  | evenDyadic => exact key 0 (fun q => rfl)
  | oddDyadic => exact key 1 (fun q => rfl)
  | evenQleR => exact key 0 (fun q => rfl)
  | oddQleR => exact key 1 (fun q => rfl)
  | evenDyadicR => exact key 0 (fun q => rfl)
  | oddDyadicR => exact key 1 (fun q => rfl)

end Reflected
end ZetaQ

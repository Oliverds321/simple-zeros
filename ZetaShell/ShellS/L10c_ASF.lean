/-
L10c_ASF (L7_10c, 3 Oct 2026): **the family functional of a near-P vector against the Farey density**
(eq:shell-assembly, first step): for `b` supported on primes `> Q` in `[Ne^{−κ}, Ne^{κ}]`,
`F(b) = Σ_{2≤q≤Q} Σ*_χ |Σ b_n χ(n)|² ≤ ∫_0^1 |S_b|² D^Ω_δ + 2π sinh κ (εQ² + N)‖b‖²`, `δ = ε/N`, `Ω` the sharp
family's weight. Lemma 1 (`signed_farey_identity`, ω = sharp; the `q = 1` term is dropped, it is `≥ 0`),
`‖Ω‖_∞ ≤ 1` (`ASc.omega_sharp_abs_le`, Tao) and Lemma 3 (`signed_gallagher`).
-/
import ZetaShell.ShellS.L10c_Tao
import ZetaShell.Farey.A3_SignedGallagher

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace ShellS
namespace ASc

open TrackF

theorem expSum_A1_eq (Nx : ℕ) (b : ℕ → ℂ) (θ : ℝ) :
    ZetaShell.expSum ((Finset.Ioc 0 Nx).filter (fun n => b n ≠ 0)) b θ = ZetaQ.expSum Nx b θ := by
  unfold ZetaShell.expSum ZetaQ.expSum ZetaQ.e
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · congr 1; congr 1; push_cast; ring
  · push Not at h; rw [h, zero_mul]

theorem charSum_A1_eq (Nx q : ℕ) (b : ℕ → ℂ) (χ : DirichletCharacter ℂ q) :
    ∑ n ∈ (Finset.Ioc 0 Nx).filter (fun n => b n ≠ 0), b n * χ (n : ZMod q) = ZetaQ.charSum q Nx b χ := by
  unfold ZetaQ.charSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs with h
  · rfl
  · push Not at h; rw [h, zero_mul]

/-- **`F(b) ≤ Σ_ξ Ω(ξ)|S_b(ξ)|²`** (Lemma 1, sharp family, `q = 1` dropped). -/
theorem famF_le_farey (Q Nx : ℕ) (b : ℕ → ℂ) (hbP : ∀ n, b n ≠ 0 → n.Prime ∧ Q < n) :
    famF (Finset.Icc 2 Q) Nx b
      ≤ ∑ x ∈ fareyIdx Q, fareyWeight .sharp Q x * ‖ZetaQ.expSum Nx b (fareyPt x)‖ ^ 2 := by
  set s := (Finset.Ioc 0 Nx).filter (fun n => b n ≠ 0) with hs
  have hsP : ∀ n ∈ s, ∀ p : ℕ, p.Prime → p ∣ n → Q < p := by
    intro n hn p hp hpn
    have hb := (Finset.mem_filter.mp hn).2
    obtain ⟨hnP, hQn⟩ := hbP n hb
    have : p = n := (Nat.prime_dvd_prime_iff_eq hp hnP).mp hpn
    rw [this]; exact hQn
  have hid := signed_farey_identity Q s b (Fam.omega .sharp Q) hsP
  -- left side
  have hL : famF (Finset.Icc 2 Q) Nx b
      ≤ ∑ q ∈ Finset.Icc 1 Q, Fam.omega .sharp Q q *
          ∑ χ ∈ primChars q, ‖∑ n ∈ s, b n * χ (n : ZMod q)‖ ^ 2 := by
    have hω : ∀ q ∈ Finset.Icc 1 Q, Fam.omega .sharp Q q = 1 := fun q hq =>
      omega_sharp_eq_one Q q (Finset.mem_Icc.mp hq).2
    rw [Finset.sum_congr rfl fun q hq => by rw [hω q hq, one_mul]]
    unfold famF
    have hsub : Finset.Icc 2 Q ⊆ Finset.Icc 1 Q := Finset.Icc_subset_Icc (by norm_num) le_rfl
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
      Finset.sum_nonneg fun χ _ => sq_nonneg _)
    refine le_of_eq (Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_)
    rw [hs, charSum_A1_eq]
  -- right side
  have hR : ∑ d ∈ Finset.Icc 1 Q, ZetaShell.OmegaW Q (Fam.omega .sharp Q) d *
        ∑ c ∈ (Finset.range d).filter (fun c => Nat.Coprime c d), ‖ZetaShell.expSum s b ((c : ℝ) / d)‖ ^ 2
      = ∑ x ∈ fareyIdx Q, fareyWeight .sharp Q x * ‖ZetaQ.expSum Nx b (fareyPt x)‖ ^ 2 := by
    unfold fareyIdx
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    have hRR : (Finset.range d).filter (fun c => Nat.Coprime c d) = ZetaQ.reducedResidues d := by
      ext c; simp [ZetaQ.reducedResidues]
    rw [hRR]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hs, expSum_A1_eq]
    rfl
  rw [← hR, ← hid]
  exact hL

/-- **F1 of the assembly**: `F(b) ≤ ∫_0^1 |S_b|² D^Ω_δ + 2π sinh κ (εQ² + N)‖b‖²`. -/
theorem famF_le_density (Q Nx : ℕ) (b : ℕ → ℂ) (hbP : ∀ n, b n ≠ 0 → n.Prime ∧ Q < n)
    (N κ ε : ℝ) (hN : 0 < N) (hκ : 0 ≤ κ) (hε : 0 < ε) (hεN : ε < N)
    (hsupp : ∀ n ∈ Finset.Ioc 0 Nx, b n ≠ 0 → N * Real.exp (-κ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ N * Real.exp κ) :
    famF (Finset.Icc 2 Q) Nx b
      ≤ (∫ θ in Set.Ico (0 : ℝ) 1, ‖ZetaQ.expSum Nx b θ‖ ^ 2
            * Ddens (fareyIdx Q) fareyPt (fareyWeight .sharp Q) (ε / N) θ)
        + 2 * Real.pi * Real.sinh κ * 1 * (ε * (Q : ℝ) ^ 2 + N) * ZetaQ.l2sq Nx b := by
  have h1 := famF_le_farey Q Nx b hbP
  have hW : ∀ x ∈ fareyIdx Q, |fareyWeight .sharp Q x| ≤ 1 := fun x _ => omega_sharp_abs_le Q x.1
  have h2 := signed_gallagher Q Nx b N κ ε hN hκ hε hεN hsupp (fareyWeight .sharp Q) 1 zero_le_one hW
  have h3 := (abs_le.mp h2).2
  linarith

end ASc
end ShellS
end ZetaShell

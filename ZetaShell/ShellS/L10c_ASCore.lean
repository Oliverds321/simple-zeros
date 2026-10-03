/-
L10c_ASCore (L7_10c, 3 Oct 2026): **the deterministic core of eq:shell-assembly at one `s`**:
for `b` supported on primes `> Q` in `[Ne^{−κ}, Ne^{κ}]`, `δ = ε/N`, the Farey weights of the sharp family,
`F(b) ≤ H′(‖b‖² − Hole) + B·Ring + B·3δ(2R₁² + πN_x)‖b‖² + 2π sinh κ(εQ² + N)‖b‖²`, where `H′ = H_w(1 + B_w·bracket)`
(Lemma 2(a), off the shells), `B = Q² + 1/δ` (Lemma 2(b), `‖Ω‖_∞ ≤ 1`), Lemma 2(c) inside holes, AF1 for spikes and
hole edges, and the hole `Hole = Σ_{r≤R₀}Σ_b ∫_{|β|≤Δ}|S(b/r+β)|²` for any `Δ < 1/(rQ)`.
-/
import ZetaShell.ShellS.L10c_ASD2
import ZetaShell.Farey.AF1_HoleEdgeMass
import ZetaShell.Lemma2.A2a_Main

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace ZetaShell
namespace ShellS
namespace ASc

open TrackF

/-- AF1 in the `β`-form of `int_split`. -/
theorem edge_le_AF1 (Q Nx R1n : ℕ) (b : ℕ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hRQ : 2 * R1n ≤ Q) :
    ∑ x ∈ X1 R1n, ((∫ β in (-(δ / 2))..(δ / 2), ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
        + (∫ β in (1 / ((x.1 : ℝ) * Q) - δ / 2)..(1 / ((x.1 : ℝ) * Q) + δ / 2),
            ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
        + ∫ β in (-(1 / ((x.1 : ℝ) * Q)) - δ / 2)..(-(1 / ((x.1 : ℝ) * Q)) + δ / 2),
            ‖ZetaQ.expSum Nx b (fareyPt x + β)‖ ^ 2)
      ≤ 3 * (2 * (δ / 2)) * (2 * (R1n : ℝ) ^ 2 + Real.pi * Nx) * ZetaQ.l2sq Nx b := by
  refine le_trans (le_of_eq ?_) (hole_edge_mass Q R1n Nx (δ / 2) b hRQ (by linarith))
  unfold X1
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun c _ => ?_
  set f : ℝ → ℝ := fun θ => ‖ZetaQ.expSum Nx b θ‖ ^ 2 with hf
  have hpt : fareyPt ⟨r, c⟩ = (c : ℝ) / r := rfl
  rw [hpt]
  have e : ∀ p q : ℝ, (∫ β in p..q, ‖ZetaQ.expSum Nx b ((c : ℝ) / r + β)‖ ^ 2)
      = ∫ θ in ((c : ℝ) / r + p)..((c : ℝ) / r + q), f θ := fun p q =>
    intervalIntegral.integral_comp_add_left f ((c : ℝ) / r)
  rw [e, e, e]
  have hs : ({-1, 0, 1} : Finset ℤ) = insert (-1) (insert 0 {1}) := rfl
  rw [hs, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e1 : ((c : ℝ) / r + -(δ / 2)) = (c : ℝ) / r + ((0 : ℤ) : ℝ) / ((r : ℝ) * Q) - δ / 2 := by push_cast; ring
  have e2 : ((c : ℝ) / r + δ / 2) = (c : ℝ) / r + ((0 : ℤ) : ℝ) / ((r : ℝ) * Q) + δ / 2 := by push_cast; ring
  have e3 : ((c : ℝ) / r + (1 / ((r : ℝ) * Q) - δ / 2)) = (c : ℝ) / r + ((1 : ℤ) : ℝ) / ((r : ℝ) * Q) - δ / 2 := by
    push_cast; ring
  have e4 : ((c : ℝ) / r + (1 / ((r : ℝ) * Q) + δ / 2)) = (c : ℝ) / r + ((1 : ℤ) : ℝ) / ((r : ℝ) * Q) + δ / 2 := by
    push_cast; ring
  have e5 : ((c : ℝ) / r + (-(1 / ((r : ℝ) * Q)) - δ / 2))
      = (c : ℝ) / r + ((-1 : ℤ) : ℝ) / ((r : ℝ) * Q) - δ / 2 := by push_cast; ring
  have e6 : ((c : ℝ) / r + (-(1 / ((r : ℝ) * Q)) + δ / 2))
      = (c : ℝ) / r + ((-1 : ℤ) : ℝ) / ((r : ℝ) * Q) + δ / 2 := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  ring

theorem ringMass_nonneg' (Q R1 N : ℕ) (K : ℝ) (a : ℕ → ℂ) : 0 ≤ ringMass Q R1 N K a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

/-- **The deterministic core of the assembly at one `s`.** -/
theorem AS_core (B₂ Q0 : ℝ) (hB₂ : 0 ≤ B₂)
    (h2a : ∀ (Q : ℕ) (N ε K Omax θ : ℝ), Q0 ≤ Q → 0 < N → 0 < ε → 1 ≤ K →
      (∀ d ∈ Finset.Icc 1 Q, |ZetaShell.OmegaW Q (Fam.omega .sharp Q) d| ≤ Omax) →
      1 ≤ R1shell Q N ε → R1shell Q N ε ≤ (Q : ℝ) / (2 * K) → θ ∉ shellSet Q K (R1shell Q N ε) →
      max (Ddens (fareyIdx Q) fareyPt (fareyWeight .sharp Q) (ε / N) θ) 0
        ≤ Hw .sharp Q * (1 + B₂ * bracket2a Q N ε K Omax (Hw .sharp Q)))
    (Q Nn : ℕ) (b : ℕ → ℂ) (N κ ε K : ℝ) (hQ0 : Q0 ≤ Q) (hN : 0 < N) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hεN : ε < N) (hK : 1 ≤ K) (hR1 : 1 ≤ R1shell Q N ε) (hR1K : R1shell Q N ε ≤ (Q : ℝ) / (2 * K))
    (hbP : ∀ n, b n ≠ 0 → n.Prime ∧ Q < n)
    (hsupp : ∀ n ∈ Finset.Ioc 0 Nn, b n ≠ 0 → N * Real.exp (-κ) ≤ (n : ℝ) ∧ (n : ℝ) ≤ N * Real.exp κ)
    (R0 Δ : ℝ) (hΔ0 : 0 ≤ Δ) (hΔh : Δ < 1 / 2) (hR0 : ⌊R0⌋₊ ≤ ⌊R1shell Q N ε⌋₊)
    (hΔr : ∀ r : ℕ, 1 ≤ r → r ≤ ⌊R0⌋₊ → Δ < 1 / ((r : ℝ) * Q)) :
    famF (Finset.Icc 2 Q) Nn b
      ≤ Hw .sharp Q * (1 + B₂ * bracket2a Q N ε K 1 (Hw .sharp Q))
          * (ZetaQ.l2sq Nn b - LemmaK.holeInt Nn b R0 Δ)
        + ((Q : ℝ) ^ 2 + N / ε) * ringMass Q ⌊R1shell Q N ε⌋₊ Nn K b
        + ((Q : ℝ) ^ 2 + N / ε) * (3 * (ε / N) * (2 * (⌊R1shell Q N ε⌋₊ : ℝ) ^ 2 + Real.pi * Nn))
            * ZetaQ.l2sq Nn b
        + 2 * Real.pi * Real.sinh κ * (ε * (Q : ℝ) ^ 2 + N) * ZetaQ.l2sq Nn b := by
  set R1r := R1shell Q N ε with hR1r
  set R1n := ⌊R1r⌋₊ with hR1n
  set δ := ε / N with hδ
  set Hp := Hw .sharp Q * (1 + B₂ * bracket2a Q N ε K 1 (Hw .sharp Q)) with hHp
  set Bm := (Q : ℝ) ^ 2 + N / ε with hBm
  have hδ0 : 0 < δ := div_pos hε hN
  have hδ1 : δ < 1 := by rw [hδ, div_lt_one hN]; exact hεN
  have hQ0' : (0 : ℝ) < Q := by
    have : (0 : ℝ) < (Q : ℝ) / (2 * K) := lt_of_lt_of_le one_pos (le_trans hR1 hR1K)
    have h2K : (0 : ℝ) < 2 * K := by linarith
    by_contra h; push Not at h
    have : (Q : ℝ) / (2 * K) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h h2K.le
    linarith
  have hR1n_le : (R1n : ℝ) ≤ R1r := Nat.floor_le (by linarith)
  have h2KR : 2 * K * R1r ≤ Q := by
    rw [le_div_iff₀ (by linarith)] at hR1K; linarith
  have hR1Q : R1n ≤ Q := by
    have : (R1n : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this
  have hsep : ∀ r r' : ℕ, 1 ≤ r → r ≤ R1n → 1 ≤ r' → r' ≤ R1n → K * ((r : ℝ) + r') ≤ Q := by
    intro r r' _ hr _ hr'
    have h1 : (r : ℝ) ≤ R1n := by exact_mod_cast hr
    have h2 : (r' : ℝ) ≤ R1n := by exact_mod_cast hr'
    nlinarith
  have hKhalf : ∀ r : ℕ, 1 ≤ r → r ≤ R1n → K / ((r : ℝ) * Q) ≤ 1 / 2 := by
    intro r hr _
    have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hW1 : ∀ d ∈ Finset.Icc 1 Q, |ZetaShell.OmegaW Q (Fam.omega .sharp Q) d| ≤ 1 :=
    fun d _ => omega_sharp_abs_le Q d
  have hbr0 : 0 ≤ bracket2a Q N ε K 1 (Hw .sharp Q) := by
    unfold bracket2a
    have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
    have hH := Hw_nonneg .sharp Q
    have t1 : 0 ≤ (1 + Real.log K) ^ 3 / K := by positivity
    have t2 : 0 ≤ N * Real.log Q ^ 2 / (ε * Q * R1shell Q N ε) := by
      have : 0 ≤ R1shell Q N ε := by linarith
      positivity
    have t3 : 0 ≤ N * Real.log Q ^ 8 / (ε * (Q : ℝ) ^ 2) := by positivity
    have t4 : 0 ≤ 1 * N / (ε * Hw .sharp Q) := by positivity
    linarith
  have hHp0 : 0 ≤ Hp := mul_nonneg (Hw_nonneg .sharp Q) (by nlinarith)
  have hBm0 : 0 ≤ Bm := by positivity
  have hoff : ∀ θ, (∀ x ∈ X1 R1n, θ ∉ nbZ Q K x) →
      Ddens (fareyIdx Q) fareyPt (fareyWeight .sharp Q) δ θ ≤ Hp := by
    intro θ hθ
    have hnot : θ ∉ shellSet Q K R1r := by
      rintro ⟨x, hx, hxR, hd⟩
      have hx' := mem_fareyIdx.mp hx
      have hxn : x.1 ≤ R1n := Nat.le_floor hxR
      exact hθ x (mem_X1.mpr ⟨⟨hx'.1.1, hxn⟩, hx'.2⟩) hd
    have := h2a Q N ε K 1 θ hQ0 hN hε hK hW1 hR1 hR1K hnot
    exact le_trans (le_max_left _ _) this
  have hall : ∀ θ, |Ddens (fareyIdx Q) fareyPt (fareyWeight .sharp Q) δ θ| ≤ Bm := by
    intro θ
    have h := lemma2b Q (fareyWeight .sharp Q) 1 δ θ hδ0 zero_le_one (fun x _ => omega_sharp_abs_le Q x.1)
    have e : 1 * ((Q : ℝ) ^ 2 + 1 / δ) = Bm := by rw [hBm, hδ, one_div_div, one_mul]
    rw [← e]; exact le_trans h.1 h.2
  have hF := famF_le_density Q Nn b hbP N κ ε hN hκ hε hεN hsupp
  have hS := int_split Q Nn R1n b K Hp Bm δ R0 Δ (fareyWeight .sharp Q) hR1Q hK hsep hKhalf hHp0 hBm0 hδ0
    (by linarith) hΔ0 hΔh hR0 hΔr hoff hall
  have hE := edge_le_AF1 Q Nn R1n b δ hδ0.le (by
    have : (2 * R1n : ℝ) ≤ Q := by nlinarith
    exact_mod_cast this)
  have hring0 := ringMass_nonneg' Q R1n Nn K b
  have hl20 : 0 ≤ ZetaQ.l2sq Nn b := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE' := mul_le_mul_of_nonneg_left hE hBm0
  have e3 : 3 * (2 * (δ / 2)) = 3 * δ := by ring
  rw [e3] at hE'
  nlinarith [mul_nonneg hHp0 hring0]

end ASc
end ShellS
end ZetaShell

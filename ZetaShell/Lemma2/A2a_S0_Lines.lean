/-
A2a_S0_Lines (L7_8, 28 Sep 2026): **Step 0 of the proof of Lemma 2(a)** (sec_shell.tex l.306–312), sorry-free.

Draft: "Take a Dirichlet approximation `a/r` of `θ` with `r ≤ R₁`, `|η| ≤ 1/(rR₁)`, `η = θ − a/r`. As `θ ∉ 𝒮`,
`u := rQ|η| ∈ [K, Q/R₁]`. Fix `a′/r′` with `ar′ − a′r = 1`. The map `(k, j) ↦ (b, q) = (ak − a′j, rk − r′j)` is a
bijection from primitive `(k, j)` with `q > 0` onto reduced fractions, and `b/q − a/r = j/(qr)`. A point with
`q ≤ Q` lies in the window `𝓘 = [θ − δ/2, θ + δ/2]` only if `0 < |j| ≤ J := Q/R₁ + R₁Qδ + 1` (or `j = 0`, the point
`a/r`)."

Proved here:
* `dirichlet_reduced`: for `R₁ ≥ 1` there are coprime `a, r` with `1 ≤ r ≤ R₁` and `|θ − a/r| ≤ 1/(rR₁)`
  (Mathlib's `Real.exists_int_int_abs_mul_sub_le`, then reduction to lowest terms).
* `u_range`: `u = rQ|η| ≤ Q/R₁`, and `u ≥ K` when `|η| ≥ K/(rQ)` (the meaning of `θ ∉ 𝒮` at `a/r`).
* `line_inverse`, `line_gcd`: the map is invertible over `ℤ` (inverse `(b, q) ↦ (r′b − a′q, rb − aq)`), and
  `gcd(b, q) = gcd(k, j)`; so it is a bijection of `ℤ²` preserving primitivity. (`q > 0` is a condition on the image.)
* `line_offset`: `b/q − a/r = j/(qr)`.
* `line_j_bound`: a point `b/q` with `0 < q ≤ Q` and `|b/q − θ| ≤ δ/2` has `|j| ≤ Q/R₁ + R₁Qδ/2` (the draft's `J` is
  larger by `R₁Qδ/2 + 1`).
-/
import Mathlib

noncomputable section

namespace ZetaShell
namespace TrackF

/-- Dirichlet approximation in lowest terms. -/
theorem dirichlet_reduced (θ R1 : ℝ) (hR1 : 1 ≤ R1) :
    ∃ a r : ℤ, 1 ≤ r ∧ (r : ℝ) ≤ R1 ∧ Int.gcd a r = 1 ∧ |θ - a / r| ≤ 1 / (r * R1) := by
  set n : ℕ := ⌊R1⌋₊ with hn
  have hn1 : 1 ≤ n := by
    rw [hn]; exact Nat.le_floor (by exact_mod_cast hR1)
  have hnR : (n : ℝ) ≤ R1 := Nat.floor_le (by linarith)
  have hRn : R1 < (n : ℝ) + 1 := Nat.lt_floor_add_one R1
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le θ (n := n) (by omega)
  set g : ℕ := Int.gcd j k with hg
  have hgpos : 0 < g := Int.gcd_pos_of_ne_zero_right j (by omega)
  have hgj : (g : ℤ) ∣ j := Int.gcd_dvd_left ..
  have hgk : (g : ℤ) ∣ k := Int.gcd_dvd_right ..
  obtain ⟨a, ha⟩ := hgj
  obtain ⟨r, hr⟩ := hgk
  have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hr0 : 0 < r := by
    have : (0 : ℤ) < g * r := by rw [← hr]; exact hk0
    exact pos_of_mul_pos_right this (by exact_mod_cast hgpos.le)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr0
  have hkr : (r : ℝ) ≤ k := by
    have : (k : ℝ) = g * r := by rw [hr]; push_cast; ring
    rw [this]
    have : (1 : ℝ) ≤ g := by exact_mod_cast hgpos
    nlinarith
  refine ⟨a, r, hr0, ?_, ?_, ?_⟩
  · have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith
  · -- gcd (j/g) (k/g) = 1
    have h := Int.gcd_div_gcd_div_gcd (i := j) (j := k) hgpos
    have ea : j / (Int.gcd j k : ℤ) = a := by
      rw [← hg, ha]; exact Int.mul_ediv_cancel_left a (by exact_mod_cast hgpos.ne')
    have er : k / (Int.gcd j k : ℤ) = r := by
      rw [← hg, hr]; exact Int.mul_ediv_cancel_left r (by exact_mod_cast hgpos.ne')
    rw [ea, er] at h
    exact h
  · have e : θ - (a : ℝ) / r = ((k : ℝ) * θ - j) / k := by
      have hj' : (j : ℝ) = g * a := by rw [ha]; push_cast; ring
      have hk' : (k : ℝ) = g * r := by rw [hr]; push_cast; ring
      rw [hj', hk']
      field_simp
    rw [e, abs_div, abs_of_pos hkR, div_le_iff₀ hkR]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / R1 := one_div_le_one_div_of_le (by linarith) hRn.le
    have h2 : 1 / ((r : ℝ) * R1) * k = (k / r) * (1 / R1) := by field_simp
    rw [h2]
    have h3 : 1 ≤ (k : ℝ) / r := by rw [le_div_iff₀ (by linarith)]; linarith
    have h4 : 0 ≤ 1 / R1 := by positivity
    nlinarith

/-- `u = rQ|η|` lies in `[K, Q/R₁]`. -/
theorem u_range (r Q R1 K η : ℝ) (hr : 0 < r) (hQ : 0 < Q) (hR1 : 0 < R1)
    (hη : |η| ≤ 1 / (r * R1)) :
    r * Q * |η| ≤ Q / R1 ∧ (K / (r * Q) ≤ |η| → K ≤ r * Q * |η|) := by
  constructor
  · have := mul_le_mul_of_nonneg_left hη (by positivity : (0 : ℝ) ≤ r * Q)
    calc r * Q * |η| ≤ r * Q * (1 / (r * R1)) := this
      _ = Q / R1 := by field_simp
  · intro h
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ r * Q)
    calc K = r * Q * (K / (r * Q)) := by field_simp
      _ ≤ r * Q * |η| := this

/-- the line map is invertible over `ℤ`. -/
theorem line_inverse (a r a' r' : ℤ) (h : a * r' - a' * r = 1) :
    (∀ k j : ℤ, r' * (a * k - a' * j) - a' * (r * k - r' * j) = k ∧
        r * (a * k - a' * j) - a * (r * k - r' * j) = j) ∧
    (∀ b q : ℤ, a * (r' * b - a' * q) - a' * (r * b - a * q) = b ∧
        r * (r' * b - a' * q) - r' * (r * b - a * q) = q) := by
  refine ⟨fun k j => ⟨?_, ?_⟩, fun b q => ⟨?_, ?_⟩⟩
  · linear_combination k * h
  · linear_combination j * h
  · linear_combination b * h
  · linear_combination q * h

/-- the line map preserves `gcd`, hence primitivity. -/
theorem line_gcd (a r a' r' : ℤ) (h : a * r' - a' * r = 1) (k j : ℤ) :
    Int.gcd (a * k - a' * j) (r * k - r' * j) = Int.gcd k j := by
  obtain ⟨h1, _⟩ := line_inverse a r a' r' h
  apply Nat.dvd_antisymm
  · have hb : ((Int.gcd (a * k - a' * j) (r * k - r' * j) : ℕ) : ℤ) ∣ a * k - a' * j := Int.gcd_dvd_left ..
    have hq : ((Int.gcd (a * k - a' * j) (r * k - r' * j) : ℕ) : ℤ) ∣ r * k - r' * j := Int.gcd_dvd_right ..
    have hk : ((Int.gcd (a * k - a' * j) (r * k - r' * j) : ℕ) : ℤ) ∣ k := by
      have e := (h1 k j).1
      have := dvd_sub (dvd_mul_of_dvd_right hb r') (dvd_mul_of_dvd_right hq a')
      rwa [e] at this
    have hj : ((Int.gcd (a * k - a' * j) (r * k - r' * j) : ℕ) : ℤ) ∣ j := by
      have e := (h1 k j).2
      have := dvd_sub (dvd_mul_of_dvd_right hb r) (dvd_mul_of_dvd_right hq a)
      rwa [e] at this
    exact Int.dvd_gcd hk hj
  · have hk : ((Int.gcd k j : ℕ) : ℤ) ∣ k := Int.gcd_dvd_left ..
    have hj : ((Int.gcd k j : ℕ) : ℤ) ∣ j := Int.gcd_dvd_right ..
    have hb : ((Int.gcd k j : ℕ) : ℤ) ∣ a * k - a' * j :=
      dvd_sub (dvd_mul_of_dvd_right hk _) (dvd_mul_of_dvd_right hj _)
    have hq : ((Int.gcd k j : ℕ) : ℤ) ∣ r * k - r' * j :=
      dvd_sub (dvd_mul_of_dvd_right hk _) (dvd_mul_of_dvd_right hj _)
    exact Int.dvd_gcd hb hq

/-- `b/q − a/r = j/(qr)` on the line `j`. -/
theorem line_offset (a r a' r' : ℤ) (h : a * r' - a' * r = 1) (k j : ℤ)
    (hq : ((r * k - r' * j : ℤ) : ℝ) ≠ 0) (hr : (r : ℝ) ≠ 0) :
    ((a * k - a' * j : ℤ) : ℝ) / ((r * k - r' * j : ℤ) : ℝ) - (a : ℝ) / r
      = (j : ℝ) / (((r * k - r' * j : ℤ) : ℝ) * r) := by
  have hR : (a : ℝ) * r' - a' * r = 1 := by exact_mod_cast h
  rw [div_sub_div _ _ hq hr]
  congr 1
  push_cast
  linear_combination (j : ℝ) * hR

/-- the `j`-range of the window: a point `a/r + β` (`β = j/(qr)`) with `0 < q ≤ Q` and `|a/r + β − θ| ≤ δ/2`, where
`|θ − a/r| ≤ 1/(rR₁)` and `0 < r ≤ R₁`, has `|j| = qr|β| ≤ Q/R₁ + R₁Qδ/2`. -/
theorem line_j_bound (r q Q R1 δ θ ar β : ℝ) (hr : 0 < r) (hrR : r ≤ R1) (hq : 0 < q) (hqQ : q ≤ Q)
    (hδ : 0 ≤ δ) (hη : |θ - ar| ≤ 1 / (r * R1)) (hwin : |ar + β - θ| ≤ δ / 2) :
    |q * r * β| ≤ Q / R1 + R1 * Q * δ / 2 := by
  have hR1 : 0 < R1 := lt_of_lt_of_le hr hrR
  have hβ : |β| ≤ 1 / (r * R1) + δ / 2 := by
    have e : β = (ar + β - θ) + (θ - ar) := by ring
    rw [e]
    calc |(ar + β - θ) + (θ - ar)| ≤ |ar + β - θ| + |θ - ar| := abs_add_le _ _
      _ ≤ δ / 2 + 1 / (r * R1) := add_le_add hwin hη
      _ = 1 / (r * R1) + δ / 2 := by ring
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q * r)]
  have hQ : 0 < Q := lt_of_lt_of_le hq hqQ
  calc q * r * |β| ≤ Q * r * (1 / (r * R1) + δ / 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hqQ hr.le) hβ (abs_nonneg _) (by positivity)
    _ = Q / R1 + r * Q * δ / 2 := by field_simp
    _ ≤ Q / R1 + R1 * Q * δ / 2 := by
        have : r * Q * δ ≤ R1 * Q * δ := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrR hQ.le) hδ
        linarith

end TrackF
end ZetaShell

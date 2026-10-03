/-
A2a_S2_CRT (L7_8, 28 Sep 2026): the local (one prime) facts behind the `δ_p` table of **Step 2 of the proof of
Lemma 2(a)** (sec_shell.tex l.323–333), sorry-free.

Draft: "For `p ∣ f`: if `p ∤ r`, `p ∣ q = rk − r′j` fixes `k mod p`; if `p ∣ r` then `p ∤ r′` and `p ∣ q ⇔ p ∣ j`.
… `δ_p = 1/p` if `p ∤ rj`, `δ_p = 1` if `p ∣ (r, j)`, and `δ_p = 0` if exactly one of `p ∣ r`, `p ∣ j` holds."
Here `ar′ − a′r = 1`, `(k, j)` primitive.

Proved:
* `line_dvd_iff_of_dvd_r`: `p ∣ r ⟹ (p ∣ rk − r′j ⇔ p ∣ j)` (gives `δ_p = 1` on `p ∣ (r, j)` and `δ_p = 0` on
  `p ∣ r, p ∤ j`);
* `line_not_dvd_of_dvd_j`: `p ∤ r`, `p ∣ j`, `(k, j)` coprime `⟹ p ∤ rk − r′j` (`δ_p = 0` on `p ∤ r, p ∣ j`);
* `line_class_unique`: `p ∤ r` ⟹ the `k` with `p ∣ rk − r′j` form at most one class mod `p`, and
  `line_class_exists`: at least one (so exactly one: `δ_p = 1/p` on `p ∤ rj`, relative to all `k`).
-/
import Mathlib

noncomputable section

namespace ZetaShell
namespace TrackF

theorem not_dvd_r'_of_dvd_r {a r a' r' p : ℤ} (h : a * r' - a' * r = 1) (hp : Prime p) (hpr : p ∣ r) :
    ¬ p ∣ r' := by
  intro hpr'
  have : p ∣ a * r' - a' * r := dvd_sub (dvd_mul_of_dvd_right hpr' a) (dvd_mul_of_dvd_right hpr a')
  rw [h] at this
  exact hp.not_isUnit (isUnit_of_dvd_one this)

theorem line_dvd_iff_of_dvd_r {a r a' r' p : ℤ} (h : a * r' - a' * r = 1) (hp : Prime p) (hpr : p ∣ r)
    (k j : ℤ) : p ∣ r * k - r' * j ↔ p ∣ j := by
  have hpr' := not_dvd_r'_of_dvd_r h hp hpr
  constructor
  · intro hq
    have h1 : p ∣ r * k := dvd_mul_of_dvd_left hpr k
    have h2 : p ∣ r' * j := by
      have := dvd_sub h1 hq
      rwa [show r * k - (r * k - r' * j) = r' * j by ring] at this
    rcases hp.dvd_or_dvd h2 with h3 | h3
    · exact absurd h3 hpr'
    · exact h3
  · intro hj
    exact dvd_sub (dvd_mul_of_dvd_left hpr k) (dvd_mul_of_dvd_right hj r')

theorem line_not_dvd_of_dvd_j {r r' p : ℤ} (hp : Prime p) (hpr : ¬ p ∣ r) (k j : ℤ) (hpj : p ∣ j)
    (hcop : IsCoprime k j) : ¬ p ∣ r * k - r' * j := by
  intro hq
  have h2 : p ∣ r * k := by
    have := dvd_add hq (dvd_mul_of_dvd_right hpj r')
    rwa [show r * k - r' * j + r' * j = r * k by ring] at this
  have hk : p ∣ k := (hp.dvd_or_dvd h2).resolve_left hpr
  obtain ⟨u, v, huv⟩ := hcop
  have : p ∣ u * k + v * j := dvd_add (dvd_mul_of_dvd_right hk u) (dvd_mul_of_dvd_right hpj v)
  rw [huv] at this
  exact hp.not_isUnit (isUnit_of_dvd_one this)

theorem line_class_unique {r r' p : ℤ} (hp : Prime p) (hpr : ¬ p ∣ r) (j k k' : ℤ)
    (hk : p ∣ r * k - r' * j) (hk' : p ∣ r * k' - r' * j) : p ∣ k - k' := by
  have : p ∣ r * (k - k') := by
    have := dvd_sub hk hk'
    rwa [show r * k - r' * j - (r * k' - r' * j) = r * (k - k') by ring] at this
  exact (hp.dvd_or_dvd this).resolve_left hpr

theorem line_class_exists {r r' p : ℤ} (hp : Prime p) (hpr : ¬ p ∣ r) (j : ℤ) :
    ∃ k : ℤ, p ∣ r * k - r' * j := by
  have hcop : IsCoprime r p := ((Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hpr).symm
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u * r' * j, ?_⟩
  refine ⟨-(v * r' * j), ?_⟩
  linear_combination (r' * j) * huv

end TrackF
end ZetaShell

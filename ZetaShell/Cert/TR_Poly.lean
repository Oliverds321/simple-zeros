/-
L7_5 (28 Sep 2026), Track R helper: soundness of the univariate list-polynomial code of `ShellCertQ`
(`padd`, `pscal`, `pmul`, `peval`, `pint`, `pdefint`, `spread`) against real evaluation and real interval integrals,
and the profile `S.p` of `ChallengeShell` as a list polynomial in `s = (2t/λ)²`.
Used by R3 (`Bshell_eq_shellBq`) and R5 (`S53L75_L75`, `D53L75_L75`).
-/
import ZetaShell.Challenge
import ZetaShell.Cert.ShellCertQ

open MeasureTheory intervalIntegral

namespace ZetaShell.TR
open ZetaShell.CertQ

/-- real evaluation of a rational coefficient list (lowest degree first), Horner as `peval`. -/
def pR (p : List ℚ) (x : ℝ) : ℝ := p.foldr (fun a acc => (a : ℝ) + x * acc) 0

@[simp] theorem pR_nil (x : ℝ) : pR [] x = 0 := rfl
@[simp] theorem pR_cons (a : ℚ) (p : List ℚ) (x : ℝ) : pR (a :: p) x = (a : ℝ) + x * pR p x := rfl

theorem pR_padd : ∀ (p q : List ℚ) (x : ℝ), pR (padd p q) x = pR p x + pR q x
  | [], q, x => by simp [padd]
  | a :: p, [], x => by simp [padd]
  | a :: p, b :: q, x => by
      simp only [padd, pR_cons, pR_padd p q x]; push_cast; ring

theorem pR_pscal (c : ℚ) : ∀ (p : List ℚ) (x : ℝ), pR (pscal c p) x = c * pR p x
  | [], x => by simp [pscal]
  | a :: p, x => by
      have ih := pR_pscal c p x
      simp only [pscal, List.map_cons, pR_cons] at ih ⊢
      rw [ih]; push_cast; ring

theorem pR_pmul : ∀ (p q : List ℚ) (x : ℝ), pR (pmul p q) x = pR p x * pR q x
  | [], q, x => by simp [pmul]
  | a :: p, q, x => by
      simp only [pmul, pR_padd, pR_pscal, pR_cons, pR_pmul p q x]; push_cast; ring

theorem pR_cast (p : List ℚ) (x : ℚ) : ((peval p x : ℚ) : ℝ) = pR p (x : ℝ) := by
  induction p with
  | nil => simp [peval]
  | cons a p ih =>
    have h : peval (a :: p) x = a + x * peval p x := rfl
    rw [h, pR_cons]; push_cast; rw [ih]

theorem continuous_pR : ∀ p : List ℚ, Continuous (pR p)
  | [] => by
      have h : pR [] = fun _ => (0 : ℝ) := rfl
      rw [h]; exact continuous_const
  | a :: p => by
      have h : pR (a :: p) = fun x => (a : ℝ) + x * pR p x := rfl
      rw [h]; exact continuous_const.add (continuous_id.mul (continuous_pR p))

theorem hasDerivAt_pintAux : ∀ (p : List ℚ) (k : ℕ) (x : ℝ),
    HasDerivAt (fun x => x ^ (k + 1) * pR (pintAux k p) x) (x ^ k * pR p x) x
  | [], k, x => by
      simp only [pintAux, pR_nil, mul_zero]; exact hasDerivAt_const x 0
  | a :: p, k, x => by
      have e : (fun x : ℝ => x ^ (k + 1) * pR (pintAux k (a :: p)) x)
          = fun x => ((a : ℝ) / ((k : ℝ) + 1)) * x ^ (k + 1)
              + x ^ (k + 1 + 1) * pR (pintAux (k + 1) p) x := by
        funext y; simp only [pintAux, pR_cons]; push_cast; ring
      rw [e]
      have h1 := (hasDerivAt_pow (k + 1) x).const_mul ((a : ℝ) / ((k : ℝ) + 1))
      have h2 := hasDerivAt_pintAux p (k + 1) x
      refine (h1.add h2).congr_deriv ?_
      show (a : ℝ) / ((k : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1)) + x ^ (k + 1) * pR p x
        = x ^ k * ((a : ℝ) + x * pR p x)
      rw [Nat.add_sub_cancel]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem hasDerivAt_pint (p : List ℚ) (x : ℝ) : HasDerivAt (pR (pint p)) (pR p x) x := by
  have e : pR (pint p) = fun x => x ^ (0 + 1) * pR (pintAux 0 p) x := by
    funext y; simp only [pint, pR_cons]; push_cast; ring
  rw [e]; simpa using hasDerivAt_pintAux p 0 x

theorem integral_pR (p : List ℚ) (a b : ℝ) :
    ∫ x in a..b, pR p x = pR (pint p) b - pR (pint p) a :=
  integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_pint p x) ((continuous_pR p).intervalIntegrable a b)

theorem cast_pdefint (p : List ℚ) (lo hi : ℚ) :
    ((pdefint p lo hi : ℚ) : ℝ) = ∫ x in (lo : ℝ)..(hi : ℝ), pR p x := by
  rw [integral_pR]; simp only [pdefint]; push_cast; rw [pR_cast, pR_cast]

/-- derivative of `pR d`, recursively. -/
def pRd : List ℚ → ℝ → ℝ
  | [], _ => 0
  | _ :: l, s => pR l s + s * pRd l s

theorem hasDerivAt_pR : ∀ (d : List ℚ) (s : ℝ), HasDerivAt (pR d) (pRd d s) s
  | [], s => by
      have h : pR [] = fun _ => (0 : ℝ) := rfl
      rw [h]; exact hasDerivAt_const s 0
  | a :: l, s => by
      have h : pR (a :: l) = fun x => (a : ℝ) + x * pR l x := rfl
      rw [h]
      have := ((hasDerivAt_id s).mul (hasDerivAt_pR l s)).const_add (a : ℝ)
      refine this.congr_deriv ?_
      show 1 * pR l s + id s * pRd l s = pR l s + s * pRd l s
      simp

theorem pR_spread : ∀ (d : List ℚ) (y : ℝ), pR (spread d) y = pR d (y ^ 2)
  | [], y => by simp [spread]
  | [a], y => by simp [spread]
  | a :: b :: l, y => by
      have h : spread (a :: b :: l) = a :: 0 :: spread (b :: l) := rfl
      rw [h, pR_cons, pR_cons, pR_spread (b :: l) y, pR_cons a (b :: l)]; push_cast; ring

theorem sum_fin_eq_pR : ∀ (d : List ℚ) (x : ℝ),
    ∑ i : Fin d.length, ((d.get i : ℚ) : ℝ) * x ^ (2 * (i : ℕ)) = pR d (x ^ 2)
  | [], x => by simp
  | a :: l, x => by
      show ∑ i : Fin (l.length + 1), (((a :: l).get i : ℚ) : ℝ) * x ^ (2 * (i : ℕ)) = _
      rw [Fin.sum_univ_succ, pR_cons, ← sum_fin_eq_pR l x, Finset.mul_sum]
      congr 1
      · simp
      · refine Finset.sum_congr rfl fun i _ => ?_
        have hg : (a :: l).get i.succ = l.get i := rfl
        rw [hg, Fin.val_succ]
        ring

theorem p_eq (S : ShellProfile) (t : ℝ) : S.p t = pR S.d ((2 * t / (S.lam : ℝ)) ^ 2) := by
  unfold ShellProfile.p; exact sum_fin_eq_pR S.d _

/-- `P̂ = (Σ d_i y^{2i})²` as in `shellBq`. -/
def Ph (S : ShellProfile) : List ℚ := pmul (spread S.d) (spread S.d)

theorem p_sq_eq (S : ShellProfile) (t : ℝ) : S.p t ^ 2 = pR (Ph S) (2 * t / (S.lam : ℝ)) := by
  rw [Ph, pR_pmul, pR_spread, p_eq]; ring

theorem p_sq_eq' (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (t : ℝ) :
    S.p t ^ 2 = pR (Ph S) (t / ((S.lam : ℝ) / 2)) := by
  rw [p_sq_eq]; congr 1; field_simp

theorem p_four_eq' (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (t : ℝ) :
    S.p t ^ 4 = pR (pmul (Ph S) (Ph S)) (t / ((S.lam : ℝ) / 2)) := by
  rw [pR_pmul, ← p_sq_eq' S hl]; ring

/-- `∫_{-λ/2}^{λ/2} f(t/(λ/2)) dt = (λ/2) ∫_{-1}^{1} f`. -/
theorem integral_scale (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) (f : ℝ → ℝ) :
    ∫ t in (-((S.lam : ℝ) / 2))..((S.lam : ℝ) / 2), f (t / ((S.lam : ℝ) / 2))
      = ((S.lam : ℝ) / 2) * ∫ y in (-1 : ℝ)..1, f y := by
  have hb : (S.lam : ℝ) / 2 ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_div _ hb, smul_eq_mul, neg_div, div_self hb]

theorem mass_eq (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) :
    S.mass = ((S.lam : ℝ) / 2) * ((pdefint (Ph S) (-1) 1 : ℚ) : ℝ) := by
  unfold ShellProfile.mass
  simp_rw [p_sq_eq' S hl]
  rw [integral_scale S hl (pR (Ph S)), cast_pdefint]; push_cast; rfl

theorem moment4_eq (S : ShellProfile) (hl : 0 < (S.lam : ℝ)) :
    ∫ t in (-((S.lam : ℝ) / 2))..((S.lam : ℝ) / 2), S.p t ^ 4
      = ((S.lam : ℝ) / 2) * ((pdefint (pmul (Ph S) (Ph S)) (-1) 1 : ℚ) : ℝ) := by
  simp_rw [p_four_eq' S hl]
  rw [integral_scale S hl (pR (pmul (Ph S) (Ph S))), cast_pdefint]; push_cast; rfl

end ZetaShell.TR

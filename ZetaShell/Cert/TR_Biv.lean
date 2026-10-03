/-
L7_5 (28 Sep 2026), Track R helper for node R3: soundness of the BIVARIATE code of `ShellCertQ`
(`qadd`, `qscal`, `qmulYB`, `shiftPoly`, `mulYpoly`, `qint`, `qevalOneSub`, `qevalMinusOne`, `psiHat`):
`pR (psiHat P) β = ∫_{-1}^{1-β} P(y) P(y+β) dy` for every real `β` (a polynomial identity; no restriction on `β`).
-/
import ZetaShell.Cert.TR_Poly

open MeasureTheory intervalIntegral

namespace ZetaShell.TR
open ZetaShell.CertQ

/-- real evaluation of a bivariate list `A(y, β)` (outer index = power of `y`, entries polynomials in `β`). -/
def qeR (A : List (List ℚ)) (y β : ℝ) : ℝ := A.foldr (fun c acc => pR c β + y * acc) 0

@[simp] theorem qeR_nil (y β : ℝ) : qeR [] y β = 0 := rfl
@[simp] theorem qeR_cons (c : List ℚ) (A : List (List ℚ)) (y β : ℝ) :
    qeR (c :: A) y β = pR c β + y * qeR A y β := rfl

theorem qeR_qadd : ∀ (A B : List (List ℚ)) (y β : ℝ), qeR (qadd A B) y β = qeR A y β + qeR B y β
  | [], B, y, β => by simp [qadd]
  | c :: A, [], y, β => by simp [qadd]
  | c :: A, d :: B, y, β => by
      simp only [qadd, qeR_cons, pR_padd, qeR_qadd A B y β]; ring

theorem qeR_qscal (c : ℚ) : ∀ (A : List (List ℚ)) (y β : ℝ), qeR (qscal c A) y β = c * qeR A y β
  | [], y, β => by simp [qscal]
  | a :: A, y, β => by
      have ih := qeR_qscal c A y β
      simp only [qscal, List.map_cons, qeR_cons, pR_pscal] at ih ⊢
      rw [ih]; ring

theorem qeR_map0 : ∀ (A : List (List ℚ)) (y β : ℝ),
    qeR (A.map (fun c => (0 : ℚ) :: c)) y β = β * qeR A y β
  | [], y, β => by simp
  | a :: A, y, β => by
      simp only [List.map_cons, qeR_cons, pR_cons, qeR_map0 A y β]; push_cast; ring

theorem qeR_qmulYB (A : List (List ℚ)) (y β : ℝ) : qeR (qmulYB A) y β = (y + β) * qeR A y β := by
  simp only [qmulYB, qeR_qadd, qeR_cons, pR_nil, qeR_map0]; ring

theorem qeR_shiftPoly : ∀ (P : List ℚ) (y β : ℝ), qeR (shiftPoly P) y β = pR P (y + β)
  | [], y, β => by simp [shiftPoly]
  | a :: P, y, β => by
      have h : shiftPoly (a :: P) = qadd [[a]] (qmulYB (shiftPoly P)) := rfl
      rw [h, qeR_qadd, qeR_qmulYB, qeR_shiftPoly P y β]
      simp only [qeR_cons, qeR_nil, pR_cons, pR_nil]; ring

theorem qeR_mulYpoly (G : List (List ℚ)) : ∀ (P : List ℚ) (y β : ℝ),
    qeR (mulYpoly P G) y β = pR P y * qeR G y β
  | [], y, β => by simp [mulYpoly]
  | a :: P, y, β => by
      have h : mulYpoly (a :: P) G = qadd (qscal a G) ([] :: mulYpoly P G) := rfl
      rw [h, qeR_qadd, qeR_qscal, qeR_cons, pR_nil, qeR_mulYpoly G P y β, pR_cons]; ring

theorem hasDerivAt_qintAux (β : ℝ) : ∀ (A : List (List ℚ)) (k : ℕ) (y : ℝ),
    HasDerivAt (fun y => y ^ (k + 1) * qeR (qintAux k A) y β) (y ^ k * qeR A y β) y
  | [], k, y => by
      simp only [qintAux, qeR_nil, mul_zero]; exact hasDerivAt_const y 0
  | a :: A, k, y => by
      have e : (fun y : ℝ => y ^ (k + 1) * qeR (qintAux k (a :: A)) y β)
          = fun y => (pR a β / ((k : ℝ) + 1)) * y ^ (k + 1)
              + y ^ (k + 1 + 1) * qeR (qintAux (k + 1) A) y β := by
        funext z; simp only [qintAux, qeR_cons, pR_pscal]; push_cast; ring
      rw [e]
      have h1 := (hasDerivAt_pow (k + 1) y).const_mul (pR a β / ((k : ℝ) + 1))
      have h2 := hasDerivAt_qintAux β A (k + 1) y
      refine (h1.add h2).congr_deriv ?_
      show pR a β / ((k : ℝ) + 1) * (((k + 1 : ℕ) : ℝ) * y ^ (k + 1 - 1)) + y ^ (k + 1) * qeR A y β
        = y ^ k * (pR a β + y * qeR A y β)
      rw [Nat.add_sub_cancel]
      have hk : (k : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring

theorem hasDerivAt_qint (A : List (List ℚ)) (β y : ℝ) :
    HasDerivAt (fun y => qeR (qint A) y β) (qeR A y β) y := by
  have e : (fun y => qeR (qint A) y β) = fun y => y ^ (0 + 1) * qeR (qintAux 0 A) y β := by
    funext z; simp only [qint, qeR_cons, pR_nil]; ring
  rw [e]; simpa using hasDerivAt_qintAux β A 0 y

theorem pR_qevalOneSub : ∀ (A : List (List ℚ)) (β : ℝ), pR (qevalOneSub A) β = qeR A (1 - β) β
  | [], β => by simp [qevalOneSub]
  | c :: A, β => by
      have h : qevalOneSub (c :: A) = padd c (pmul [1, -1] (qevalOneSub A)) := rfl
      rw [h, pR_padd, pR_pmul, pR_qevalOneSub A β, qeR_cons]
      simp only [pR_cons, pR_nil]; push_cast; ring

theorem pR_qevalMinusOne : ∀ (A : List (List ℚ)) (β : ℝ), pR (qevalMinusOne A) β = qeR A (-1) β
  | [], β => by simp [qevalMinusOne]
  | c :: A, β => by
      have h : qevalMinusOne (c :: A) = padd c (pscal (-1) (qevalMinusOne A)) := rfl
      rw [h, pR_padd, pR_pscal, pR_qevalMinusOne A β, qeR_cons]; push_cast; ring

/-- **soundness of `psiHat`**: `ψ̂(β) = ∫_{-1}^{1-β} P(y) P(y+β) dy` as a real identity, every `β`. -/
theorem pR_psiHat (P : List ℚ) (β : ℝ) :
    pR (psiHat P) β = ∫ y in (-1 : ℝ)..(1 - β), pR P y * pR P (y + β) := by
  have hd : ∀ y, HasDerivAt (fun y => qeR (qint (mulYpoly P (shiftPoly P))) y β)
      (pR P y * pR P (y + β)) y := by
    intro y
    have := hasDerivAt_qint (mulYpoly P (shiftPoly P)) β y
    rwa [qeR_mulYpoly, qeR_shiftPoly] at this
  have hc : Continuous (fun y => pR P y * pR P (y + β)) :=
    (continuous_pR P).mul ((continuous_pR P).comp (continuous_add_const β))
  rw [integral_eq_sub_of_hasDerivAt (fun y _ => hd y) (hc.intervalIntegrable _ _)]
  simp only [psiHat, pR_padd, pR_pscal, pR_qevalOneSub, pR_qevalMinusOne]; push_cast; ring

end ZetaShell.TR

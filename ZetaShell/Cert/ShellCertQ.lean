/-
lean_work/L7_1/ShellCertQ.lean — L7_1, 28 Sep 2026. Track R, the NUMERICAL half of the Shell certificate, in core
Lean only (no Mathlib; `Rat` is core's `Init.Data.Rat`, the same type as Mathlib's `ℚ`).

`shellBq S` is the exact rational `B_{α′}(v_p)` of ssec:shell-cert "Method" (sec_shell.tex l.1025–1031),
computed in y-units (`t = (λ/2)·y`, so `p(t) = Σ d_i y^{2i}` and no power of `λ` enters the polynomials):

  B = [ψ̂(0)/b + 2b ∫_0^{1/b} β ψ̂ + 2ℓ ∫_{1/b}^{α′/b} ψ̂ + 2C⁺ ∫_{α′/b}^{2} ψ̂] / Z²,    b = λ/2,
  P̂(y) = (Σ_i d_i y^{2i})²,  Z = ∫_{−1}^{1} P̂,  ψ̂(β) = ∫_{−1}^{1−β} P̂(y) P̂(y+β) dy  (a polynomial of degree 49).

Python mirror: `shell_cert_y.py` (reproduces R8-2's independent `check_profile.py` value EXACTLY for S53-L75 and
D53-L75; about 2·10⁴ rational operations; coefficients of ψ̂ have ≈ 213-digit numerators and denominators).
The ANALYTIC half — `Bshell ℓ α′ C⁺ v_p = shellBq S` for the real-valued functional of `ChallengeShell` — is node R3
(`skeleton/R3_ShellPayoffFormula.lean`), not proved here.
Level: A (kernel only, `decide +kernel`; no `native_decide`).
-/

namespace ZetaShell.CertQ

/-- polynomials in one variable, coefficient lists, lowest degree first. -/
def padd : List Rat → List Rat → List Rat
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

def pscal (c : Rat) (p : List Rat) : List Rat := p.map (fun a => c * a)

def pmul : List Rat → List Rat → List Rat
  | [], _ => []
  | a :: p, q => padd (pscal a q) (0 :: pmul p q)

def peval (p : List Rat) (x : Rat) : Rat := p.foldr (fun a acc => a + x * acc) 0

def pintAux : Nat → List Rat → List Rat
  | _, [] => []
  | k, a :: p => (a / ((k + 1 : Nat) : Rat)) :: pintAux (k + 1) p

/-- antiderivative vanishing at 0. -/
def pint (p : List Rat) : List Rat := 0 :: pintAux 0 p

def pdefint (p : List Rat) (lo hi : Rat) : Rat := peval (pint p) hi - peval (pint p) lo

/-- bivariate polynomials `A(y, β)`: list indexed by the power of `y`, entries polynomials in `β`. -/
def qadd : List (List Rat) → List (List Rat) → List (List Rat)
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => padd a b :: qadd p q

/-- `(y + β) · A`. -/
def qmulYB (A : List (List Rat)) : List (List Rat) := qadd ([] :: A) (A.map (fun c => 0 :: c))

def qscal (c : Rat) (A : List (List Rat)) : List (List Rat) := A.map (pscal c)

/-- `P(y + β)` by Horner in `y + β`. -/
def shiftPoly (P : List Rat) : List (List Rat) := P.foldr (fun a acc => qadd [[a]] (qmulYB acc)) []

/-- `P(y) · G(y, β)` by Horner in `y`. -/
def mulYpoly (P : List Rat) (G : List (List Rat)) : List (List Rat) :=
  P.foldr (fun a acc => qadd (qscal a G) ([] :: acc)) []

def qintAux : Nat → List (List Rat) → List (List Rat)
  | _, [] => []
  | k, a :: p => pscal (1 / ((k + 1 : Nat) : Rat)) a :: qintAux (k + 1) p

/-- antiderivative in `y`. -/
def qint (A : List (List Rat)) : List (List Rat) := [] :: qintAux 0 A

/-- `A(1 − β, β)`. -/
def qevalOneSub (A : List (List Rat)) : List Rat := A.foldr (fun c acc => padd c (pmul [1, -1] acc)) []

/-- `A(−1, β)`. -/
def qevalMinusOne (A : List (List Rat)) : List Rat := A.foldr (fun c acc => padd c (pscal (-1) acc)) []

/-- `d ↦ Σ d_i y^{2i}`. -/
def spread : List Rat → List Rat
  | [] => []
  | [a] => [a]
  | a :: l => a :: 0 :: spread l

/-- `ψ̂(β) = ∫_{−1}^{1−β} P̂(y) P̂(y+β) dy`. -/
def psiHat (Ph : List Rat) : List Rat :=
  let A := qint (mulYpoly Ph (shiftPoly Ph))
  padd (qevalOneSub A) (pscal (-1) (qevalMinusOne A))

/-- the exact rational `B_{α′}(v_p)` for the data `(λ, α′, ℓ, C⁺, d)`. -/
def shellBq (lam alphaP level Cplus : Rat) (d : List Rat) : Rat :=
  let b := lam / 2
  let ph := spread d
  let Ph := pmul ph ph
  let Z := pdefint Ph (-1) 1
  let ps := psiHat Ph
  (peval ps 0 / b + 2 * b * pdefint (pmul [0, 1] ps) 0 (1 / b)
    + 2 * level * pdefint ps (1 / b) (alphaP / b) + 2 * Cplus * pdefint ps (alphaP / b) 2) / (Z * Z)

/-- S53-L75 (sec_shell.tex l.1224). -/
def dS53 : List Rat :=
  [1, -109245641 / 315967035, -484609675 / 903872491, 1126440115 / 499347366,
   -1244916364 / 475100341, 381673291 / 981251350, 37853428 / 698475165]

/-- D53-L75 (sec_shell.tex l.1230). -/
def dD53 : List Rat :=
  [1, -390353034 / 798066593, 1309177511 / 918253499, -6068806879 / 896328244,
   13364613432 / 870778397, -12836034741 / 854019032, 4242100897 / 905838731]

def BS53 : Rat := shellBq (191 / 100) (2497 / 1500) 1 (541161617 / 100000000) dS53

def BD53 : Rat := shellBq (93 / 50) (2497 / 1500) 1 (721548823 / 100000000) dD53

/-- **Track R, numerical half, S53-L75**: `B ≤ 2 − 0.9059137927` (slack `3.79·10⁻¹¹`). Kernel only. -/
theorem BS53_le : BS53 ≤ 2 - 9059137927 / 10000000000 := by decide +kernel

/-- **Track R, numerical half, D53-L75**: `B ≤ 2 − 0.9031776196` (slack `9.18·10⁻¹¹`). Kernel only. -/
theorem BD53_le : BD53 ≤ 2 - 9031776196 / 10000000000 := by decide +kernel

/-- negative control: the next 10-digit claim `0.9059137928` is FALSE (the kernel really evaluates `BS53`). -/
theorem BS53_not_le_next : ¬ (BS53 ≤ 2 - 9059137928 / 10000000000) := by decide +kernel

/-- negative control for D53-L75: `0.9031776197` is FALSE. -/
theorem BD53_not_le_next : ¬ (BD53 ≤ 2 - 9031776197 / 10000000000) := by decide +kernel

/-- negative control on the kernel constant: with `C⁺ + 10⁻⁶` the S53 claim fails. -/
theorem BS53_Cplus_control :
    ¬ (shellBq (191 / 100) (2497 / 1500) 1 (541161617 / 100000000 + 1 / 1000000) dS53
        ≤ 2 - 9059137927 / 10000000000) := by decide +kernel

/-! ## Track R, numerical half of node R5 (the L75 side conditions), in `s = (2t/λ)²`

`p = q(s)`, `q(s) = Σ d_i s^i`. On `s ∈ [0,1]`: `q > 0`, `(1 − q)/s = −Σ_{i≥1} d_i s^{i−1} > 0` (so `p ≤ 1`), and
`−q′(s) > 0` (so `p` strictly decreasing in `t ∈ [0, λ/2]`), each by POSITIVE BERNSTEIN COEFFICIENTS on `[0,1]` after
`e` degree elevations (the sufficient test of `ZetaQ.Payoff.Cert.NonnegOK`, whose soundness lemma
`evalPoly_nonneg_of_bernstein` is the template of R5's analytic half); and the exact moments
`a = ⟨p²⟩ = Z/2 ≥ 3/4`, `b = ⟨p⁴⟩ = ½∫_{−1}^{1} P̂² ≥ 1/2`, `p(λ/2) = Σ d_i ≥ 1/6` (y-units as above). -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def chooseQ (n k : Nat) : Rat := ((fact n / (fact k * fact (n - k)) : Nat) : Rat)

/-- Bernstein coefficients on `[0,1]` of `Σ c_i s^i` (degree `n = c.length − 1`). -/
def bernCoeffs (c : List Rat) : List Rat :=
  let n := c.length - 1
  (List.range (n + 1)).map fun (k : Nat) =>
    ((List.range (k + 1)).map fun (i : Nat) => chooseQ k i / chooseQ n i * c.getD i 0).foldr (· + ·) 0

/-- one degree elevation of a Bernstein coefficient list. -/
def elevate (b : List Rat) : List Rat :=
  let m : Nat := b.length - 1
  (List.range (m + 2)).map fun (k : Nat) =>
    let lo : Rat := if k = 0 then 0 else b.getD (k - 1) 0
    let wlo : Rat := ((k : Nat) : Rat) / ((m + 1 : Nat) : Rat)
    let whi : Rat := ((m + 1 - k : Nat) : Rat) / ((m + 1 : Nat) : Rat)
    wlo * lo + whi * b.getD k 0

def elevateN : Nat → List Rat → List Rat
  | 0, b => b
  | e + 1, b => elevateN e (elevate b)

def allPos (b : List Rat) : Bool := b.all fun x => decide (0 < x)

def l75Check (d : List Rat) (e : Nat) : Bool :=
  let om := (d.drop 1).map (fun x => -x)
  let dq := ((d.drop 1).zipIdx.map fun (x, i) => -(((i + 1 : Nat) : Rat) * x))
  let ph := spread d
  let Ph := pmul ph ph
  let Z := pdefint Ph (-1) 1
  let Z2 := pdefint (pmul Ph Ph) (-1) 1
  allPos (elevateN e (bernCoeffs d)) && allPos (elevateN e (bernCoeffs om))
    && allPos (elevateN e (bernCoeffs dq))
    && decide ((3 : Rat) / 4 ≤ Z / 2) && decide ((1 : Rat) / 2 ≤ Z2 / 2)
    && decide ((1 : Rat) / 6 ≤ d.foldr (· + ·) 0)

/-- **R5, numerical half, S53-L75** (level A, kernel). -/
theorem l75_S53 : l75Check dS53 10 = true := by decide +kernel

/-- **R5, numerical half, D53-L75** (level A, kernel; `−p′` needs the 10 elevations). -/
theorem l75_D53 : l75Check dD53 10 = true := by decide +kernel

/-- negative control: without elevation the D53-L75 derivative test fails (it is only sufficient). -/
theorem l75_D53_noelev : l75Check dD53 0 = false := by decide +kernel

end ZetaShell.CertQ

#print axioms ZetaShell.CertQ.BS53_le
#print axioms ZetaShell.CertQ.BD53_le
#print axioms ZetaShell.CertQ.BS53_not_le_next
#print axioms ZetaShell.CertQ.l75_S53
#print axioms ZetaShell.CertQ.l75_D53

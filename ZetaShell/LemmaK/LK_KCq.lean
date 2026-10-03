/-
lean_work/L7_3/skeleton/LK_KCq.lean — L7_3, 28 Sep 2026. Node KC, NUMERICAL half: the exact rational killed-kernel
functional `B^K_{C⁺}(v_p)` of the Theorem 1′ profiles, in core Lean only (no Mathlib; `Rat` is core's), by
`decide +kernel`. Level A.

The algorithm is L7_1's y-unit evaluation (`lean_work/L7_1/ShellCertQ.lean`, `shellBq`; copied verbatim below into
this namespace, credit L7_1), used with `α′ = 1`: then the level term `∫_{1/b}^{α′/b}` is empty and
  B^K = [ψ̂(0)/b + 2b ∫_0^{1/b} β ψ̂ + 2C⁺ ∫_{1/b}^{2} ψ̂] / Z²,   b = λ/2,
which is eq:BK in y-units (`t = b·y`; `ψ(α) = ψ̂(α/b)/(bZ²)`). Profiles are given as in tab:K-profiles
(`p(t) = Σ cᵢ t^{2i}`) and converted by `dᵢ = cᵢ b^{2i}`.
Calibration against the independent Python evaluator (R5-4's `exactB.py`, Fraction arithmetic, t-units):
the draft's profile (iv′) at `λ = 32/25` gives `0.723757382394…` (R5-4 exactB; tab:K-data prints it rounded as 0.7237573824)
— bracketed below to 10⁻¹⁰.
The ANALYTIC half (the real integral `BK C⁺ S.v` equals this rational) is the rest of node KC, as L7_1's R3.
-/

namespace ZetaShell.LemmaK.CertQ

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

def pint (p : List Rat) : List Rat := 0 :: pintAux 0 p

def pdefint (p : List Rat) (lo hi : Rat) : Rat := peval (pint p) hi - peval (pint p) lo

def qadd : List (List Rat) → List (List Rat) → List (List Rat)
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => padd a b :: qadd p q

def qmulYB (A : List (List Rat)) : List (List Rat) := qadd ([] :: A) (A.map (fun c => 0 :: c))

def qscal (c : Rat) (A : List (List Rat)) : List (List Rat) := A.map (pscal c)

def shiftPoly (P : List Rat) : List (List Rat) := P.foldr (fun a acc => qadd [[a]] (qmulYB acc)) []

def mulYpoly (P : List Rat) (G : List (List Rat)) : List (List Rat) :=
  P.foldr (fun a acc => qadd (qscal a G) ([] :: acc)) []

def qintAux : Nat → List (List Rat) → List (List Rat)
  | _, [] => []
  | k, a :: p => pscal (1 / ((k + 1 : Nat) : Rat)) a :: qintAux (k + 1) p

def qint (A : List (List Rat)) : List (List Rat) := [] :: qintAux 0 A

def qevalOneSub (A : List (List Rat)) : List Rat := A.foldr (fun c acc => padd c (pmul [1, -1] acc)) []

def qevalMinusOne (A : List (List Rat)) : List Rat := A.foldr (fun c acc => padd c (pscal (-1) acc)) []

def spread : List Rat → List Rat
  | [] => []
  | [a] => [a]
  | a :: l => a :: 0 :: spread l

def psiHat (Ph : List Rat) : List Rat :=
  let A := qint (mulYpoly Ph (shiftPoly Ph))
  padd (qevalOneSub A) (pscal (-1) (qevalMinusOne A))

def shellBq (lam alphaP level Cplus : Rat) (d : List Rat) : Rat :=
  let b := lam / 2
  let ph := spread d
  let Ph := pmul ph ph
  let Z := pdefint Ph (-1) 1
  let ps := psiHat Ph
  (peval ps 0 / b + 2 * b * pdefint (pmul [0, 1] ps) 0 (1 / b)
    + 2 * level * pdefint ps (1 / b) (alphaP / b) + 2 * Cplus * pdefint ps (alphaP / b) 2) / (Z * Z)

/-- `dᵢ = cᵢ (λ/2)^{2i}`: from the `t^{2i}` coefficients of tab:K-profiles to y-units. -/
def toD (lam : Rat) (c : List Rat) : List Rat :=
  c.zipIdx.map fun (x, i) => x * (lam / 2) ^ (2 * i)

/-- the exact rational `B^K_{C⁺}(v_p)` (killed kernel = `shellBq` at `α′ = 1`). -/
def killedBq (lam Cplus : Rat) (c : List Rat) : Rat := shellBq lam 1 0 Cplus (toD lam c)

def lamStarQ : Rat := 2501464303 / 2000000000
def CplusQ : Rat := 541161617 / 100000000

/-- ZetaQ's `designProfileQle` (DesignProfile.lean). -/
def cDesign : List Rat := [1, -81257 / 125000, 3458583 / 1000000, -3669851 / 200000]

/-- the degree-8 killed profile at `λ*` (L7_3 `numerics/incap_opt.out`). -/
def cLam8 : List Rat :=
  [1, -204581936 / 297214369, 2511259929 / 554894287, -16394872054 / 595414977, 14897653256 / 697578907]

/-- the draft's profile (iv′) at `λ = 32/25` (tab:K-profiles), for calibration only. -/
def cIvPrime : List Rat :=
  [1, -602328709 / 950098261, 2849572522 / 801260219, -22475130839 / 995987536, 9194235913 / 679998771]

def BKdesign : Rat := killedBq lamStarQ CplusQ cDesign
def BKlam8 : Rat := killedBq lamStarQ CplusQ cLam8
def BKivPrime : Rat := killedBq (32 / 25) CplusQ cIvPrime

/-- **KC (a), numerical half**: `2 − B^K ≥ 0.7235 + 1.1·10⁻⁵` at ZetaQ's design profile. -/
theorem BKdesign_le : BKdesign ≤ 2 - 7235 / 10000 - 11 / 1000000 := by decide +kernel

/-- control: `0.7235 + 1.2·10⁻⁵` is FALSE (exact value 0.72351108…). -/
theorem BKdesign_not_le : ¬ (BKdesign ≤ 2 - 7235 / 10000 - 12 / 1000000) := by decide +kernel

/-- **KC (b), numerical half**: `2 − B^K ≥ 0.7237 + 4.9·10⁻⁵` at the degree-8 profile at `λ*`. -/
theorem BKlam8_le : BKlam8 ≤ 2 - 7237 / 10000 - 49 / 1000000 := by decide +kernel

/-- control: the lead's `0.72375` is NOT certified by this profile (exact value 0.72374950…). -/
theorem BKlam8_not_72375 : ¬ (BKlam8 ≤ 2 - 72375 / 100000) := by decide +kernel

/-- calibration: (iv′) at `λ = 32/25` gives `2 − B^K ≥ 0.7237573823` (exact 0.723757382394…; tab:K-data prints the ROUNDED 0.7237573824). -/
theorem BKivPrime_le : BKivPrime ≤ 2 - 7237573823 / 10000000000 := by decide +kernel

/-- calibration, upper side: `2 − B^K < 0.7237573824`. -/
theorem BKivPrime_not_le : ¬ (BKivPrime ≤ 2 - 7237573824 / 10000000000) := by decide +kernel

/-! ## The side conditions, numerical half (L7_1's `l75Check`, copied verbatim, credit L7_1)
In `s = y² = (2t/λ)²`, `p = q(s)`: `q > 0`, `(1 − q)/s > 0`, `−q′ > 0` on `[0,1]` by positive Bernstein coefficients after
`e` elevations, and the exact moments `a = Z/2 ≥ 3/4`, `b ≥ 1/2`, `p(λ/2) = Σ dᵢ ≥ 1/6`. -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def chooseQ (n k : Nat) : Rat := ((fact n / (fact k * fact (n - k)) : Nat) : Rat)

def bernCoeffs (c : List Rat) : List Rat :=
  let n := c.length - 1
  (List.range (n + 1)).map fun (k : Nat) =>
    ((List.range (k + 1)).map fun (i : Nat) => chooseQ k i / chooseQ n i * c.getD i 0).foldr (· + ·) 0

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

/-- side conditions of ZetaQ's design profile at `λ*` (numerical half; the tree proves `ProfileQ` analytically). -/
theorem side_design : l75Check (toD lamStarQ cDesign) 10 = true := by decide +kernel

/-- side conditions of the degree-8 profile at `λ*` (numerical half). -/
theorem side_lam8 : l75Check (toD lamStarQ cLam8) 10 = true := by decide +kernel

end ZetaShell.LemmaK.CertQ

#print axioms ZetaShell.LemmaK.CertQ.BKdesign_le
#print axioms ZetaShell.LemmaK.CertQ.BKlam8_le
#print axioms ZetaShell.LemmaK.CertQ.BKlam8_not_72375
#print axioms ZetaShell.LemmaK.CertQ.BKivPrime_le
#print axioms ZetaShell.LemmaK.CertQ.BKivPrime_not_le
#print axioms ZetaShell.LemmaK.CertQ.BKdesign_not_le
#print axioms ZetaShell.LemmaK.CertQ.side_design
#print axioms ZetaShell.LemmaK.CertQ.side_lam8

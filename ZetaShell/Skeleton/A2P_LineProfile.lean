/-
Node A2P (L7_8, 28 Sep 2026): **Lemma P, universality of the line profile** (lem:shell-P, sec_shell.tex l.357–386;
the profile `g_r` is defined in the proof of Lemma 2, Step 4, l.343–347; `𝔈_{j,r}(e)` in Step 3, l.336).

Draft: "For all `r ≥ 1`, `v ≥ 1`: `|g_r(v) − ḡ_w| ≤ B_w(1 + log v)²/v`, where `ḡ_w = W₁ Σ_e c_e Π(e)/e²` and
`Π(e) = ∏_p (1 − 1/p)(1 + h_e(p)/p)` is independent of `r`. Moreover `ḡ_w = W₁·36/π⁴` (plain) and `ḡ_w = W₁·𝔖`
(`q/φ` kind)", with `g_r(v) = v⁻² Σ_{1≤j≤v} φ(j) Σ_e c_e w(je/v) 𝔈_{j,r}(e)`,
`𝔈_{j,r}(e) = ∏_{p∤rj}(1 + λ_e(p)/p) ∏_{p|(r,j)} h_e(p)`, `λ_e(p) = h_e(p) − 1`.

Lean form (the three families of l.279–281 only; they are the only ones the paper uses):
* `Fam` = sharp (`w = 1_{[0,1]}`, plain), dyadic (`w = 1_{(1/2,1]}`, plain), weighted (`w = (1−x)²` on `[0,1]`,
  `q/φ` kind); `c_e = μ(e)/e` (plain), `μ(e)/φ(e)` (`q/φ`); `h_e(p) = (1 − 1/p)·1[p∤e]` (plain), `1[p∤e]` (`q/φ`).
* `Ecoef k r j e` is `𝔈_{j,r}(e)` in closed form. Plain kind: `∏_{p∤rj}(1+λ_e(p)/p) = ∏_{p∤rje}(1−p⁻²)·∏_{p|e,p∤rj}(1−1/p)
  = (6/π²)·∏_{p|rje}(1−p⁻²)⁻¹·∏_{p|e,p∤rj}(1−1/p)` (Euler product `∏_p(1−p⁻²) = 6/π²`); `q/φ` kind:
  `∏_{p|e,p∤rj}(1−1/p)` (finite). The identification with the draft's infinite product is the Euler product for
  `ζ(2)` (Mathlib `riemannZeta_two`, Euler product); it is a definition here, recorded as such.
* the `e`-sum is over `1 ≤ e ≤ ⌊v⌋` (for `e > v`, `je/v > 1` and `w = 0`: no terms dropped).
* `ḡ` of the `q/φ` kind uses `Sconst = ∏'_p (1 − p⁻² − p⁻³)` (`tprod`); its faithfulness needs multipliability,
  proved as `Sconst_multipliable` (sorry-free).
Proved here (sorry-free): the local identities of the proof, step (iii) (`euler_factor_pnr`, `euler_factor_pr`) and
the two evaluations (`euler_eval_plain`, `euler_eval_qphi`).
Numerics: `numerics/lemmaP_test.py` (`lemmaP_test.out`): exact rationals times `6/π²`, mpmath 40 digits; 16 values of
`r` (1, 2, 3, 4, 6, 12, 30, 210, 2310, 30030, 97, 997, 10007, 2·10007, 101·103·107, 1009·1013·1019·1021), 52 values
of `v ∈ [1, 1000]`: worst `|g_r(v) − ḡ|·v/(1+log v)²` = 0.7988 (sharp), 0.8450 (dyadic), 0.0399 (weighted), all at
`v = 1`; at `v = 1000` it is ≤ 0.0043. No violation with `B_w = 1`.
-/
import ZetaShell.Defs.TF_Defs
import ZetaShell.Lemma2.L711_MuSqPhi
import ZetaShell.Lemma2.A2P_LineSumCore
import ZetaQ.Normalisation

noncomputable section
open scoped BigOperators

namespace ZetaShell
namespace TrackF

/-- the two kinds of family (sec_shell l.277). -/
inductive FKind | plain | qphi

/-- the three families used (sec_shell l.279–281). -/
inductive Fam | sharp | dyadic | weighted

def Fam.kind : Fam → FKind
  | .sharp => .plain
  | .dyadic => .plain
  | .weighted => .qphi

/-- the profile `w`, supported in `[0,1]`. -/
def Fam.w : Fam → ℝ → ℝ
  | .sharp => fun x => if 0 ≤ x ∧ x ≤ 1 then 1 else 0
  | .dyadic => fun x => if 1 / 2 < x ∧ x ≤ 1 then 1 else 0
  | .weighted => fun x => if 0 ≤ x ∧ x ≤ 1 then (1 - x) ^ 2 else 0

/-- `W₁ = ∫₀¹ x w(x) dx`. -/
def Fam.W1 : Fam → ℝ
  | .sharp => 1 / 2
  | .dyadic => 3 / 8
  | .weighted => 1 / 12

/-- `c_e`. -/
def cE (k : FKind) (e : ℕ) : ℝ :=
  match k with
  | .plain => ((ArithmeticFunction.moebius e : ℤ) : ℝ) / (e : ℝ)
  | .qphi => ((ArithmeticFunction.moebius e : ℤ) : ℝ) / (Nat.totient e : ℝ)

/-- `h_e(p)` at a prime `p`. -/
def hE (k : FKind) (e p : ℕ) : ℝ :=
  match k with
  | .plain => if p ∣ e then 0 else 1 - 1 / (p : ℝ)
  | .qphi => if p ∣ e then 0 else 1

/-- `𝔈_{j,r}(e)` (Step 3), closed form. -/
def Ecoef (k : FKind) (r j e : ℕ) : ℝ :=
  (match k with
    | .plain => (6 / Real.pi ^ 2) * ∏ p ∈ (r * j * e).primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹
    | .qphi => 1) *
  (∏ p ∈ e.primeFactors.filter (fun p => ¬ p ∣ r * j), (1 - 1 / (p : ℝ))) *
  ∏ p ∈ (Nat.gcd r j).primeFactors, hE k e p

/-- the line profile `g_r(v) = v⁻² Σ_{1≤j≤v} φ(j) Σ_e c_e w(je/v) 𝔈_{j,r}(e)` (Step 4). -/
def gProf (F : Fam) (r : ℕ) (v : ℝ) : ℝ :=
  (v ^ 2)⁻¹ * ∑ j ∈ Finset.Icc 1 ⌊v⌋₊, (Nat.totient j : ℝ) *
    ∑ e ∈ Finset.Icc 1 ⌊v⌋₊, cE F.kind e * F.w ((j : ℝ) * e / v) * Ecoef F.kind r j e

/-- `𝔖 = ∏_p (1 − p⁻² − p⁻³)`. -/
def Sconst : ℝ := ∏' p : Nat.Primes, (1 - 1 / ((p : ℕ) : ℝ) ^ 2 - 1 / ((p : ℕ) : ℝ) ^ 3)

/-- `ḡ_w`: `W₁·36/π⁴` (plain), `W₁·𝔖` (`q/φ`). -/
def gbar (F : Fam) : ℝ :=
  match F.kind with
  | .plain => F.W1 * (36 / Real.pi ^ 4)
  | .qphi => F.W1 * Sconst

/-- faithfulness obligation for `Sconst` (`tprod` is `1` on non-multipliable families). -/
theorem Sconst_multipliable :
    Multipliable (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2 - 1 / ((p : ℕ) : ℝ) ^ 3)) := by
  have hs : Summable (fun n : ℕ => 2 * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 2
  have hsP : Summable (fun p : Nat.Primes => 2 * (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective Subtype.val_injective
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖(-(1 / ((p : ℕ) : ℝ) ^ 2) - 1 / ((p : ℕ) : ℝ) ^ 3)‖) := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hsP
    have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have h2 : 0 < 1 / ((p : ℕ) : ℝ) ^ 2 := by positivity
    have h3 : 0 < 1 / ((p : ℕ) : ℝ) ^ 3 := by positivity
    have h32 : 1 / ((p : ℕ) : ℝ) ^ 3 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    rw [Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have hm := multipliable_one_add_of_summable hnorm
  have e : (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2 - 1 / ((p : ℕ) : ℝ) ^ 3))
      = (fun p : Nat.Primes => 1 + (-(1 / ((p : ℕ) : ℝ) ^ 2) - 1 / ((p : ℕ) : ℝ) ^ 3)) := by
    funext p
    ring
  rw [e]
  exact hm

/-! ### L7_11 (round 2): `lemmaP` derived from three sub-nodes

`g_r(v) = v⁻² Σ_{e≤v} c_e S_e(v/e)`, `S_e(y) = Σ_{j≤y} φ(j) 𝔈_{j,r}(e) w(j/y)`. Sub-nodes:
* `line_sum_asymp` (OPEN): `|S_e(y) − y² W₁ Π(e)| ≤ C τ(e) y (1 + log y)²`, uniformly in `r ≥ 1`, `e ≥ 1`, `y ≥ 1`
  (the draft's steps (ii)–(iii) plus the partial summation against `w`);
* `tail_sum` (PROVED): `|W₁ Σ_{e≤v} c_e Π(e)/e² − ḡ| ≤ C/v` (the Euler product `Σ_e c_e Π(e)/e² = ḡ/W₁`, via
  Mathlib's `EulerProduct.eulerProduct_hasProd` and the trunk's `N2.hasSum_mu_sq`, and its tail);
* `sum_cE_tau` (PROVED): `Σ_{e≤N} |c_e| τ(e)/e ≤ C` (from the shared `L711_MuSqPhi`).
`Π(e) = ∏_p (1 − 1/p)(1 + h_e(p)/p)` in closed form: `Π₀ ∏_{p|e}(1 + 1/p − 1/p²)⁻¹`, `Π₀ = ∏_p (1 − 2/p² + 1/p³)`
(plain), `(6/π²) ∏_{p|e}(1 + 1/p)⁻¹` (`q/φ`). Both sub-nodes tested: `numerics/lemmaP_split_test.py`.
Only `line_sum_asymp` is open. -/

theorem Fam.w_zero_gt_one_P (F : Fam) {x : ℝ} (hx : 1 < x) : F.w x = 0 := by
  cases F <;> simp only [Fam.w] <;> rw [if_neg (by intro h; linarith [h.2])]

/-- `Π₀ = ∏_p (1 − 2/p² + 1/p³)`. -/
def Pi0plain : ℝ := ∏' p : Nat.Primes, (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)

/-- `Π(e)` in closed form. -/
def PiE (k : FKind) (e : ℕ) : ℝ :=
  match k with
  | .plain => Pi0plain * ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹
  | .qphi => (6 / Real.pi ^ 2) * ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹

/-- **Sub-node (PROVED, L7_8c, 3 Oct; proof in `A2P_LineSumCore`).** The line sum against `w`, uniformly in `r`. -/
theorem line_sum_asymp (F : Fam) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℕ, 1 ≤ r → ∀ e : ℕ, 1 ≤ e → ∀ y : ℝ, 1 ≤ y →
    |∑ j ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient j : ℝ) * Ecoef F.kind r j e * F.w ((j : ℝ) / y)
      - y ^ 2 * F.W1 * PiE F.kind e| ≤ C * (e.divisors.card : ℝ) * (y * (1 + Real.log y) ^ 2) := by
  cases F
  · exact lsc_line_sharp
  · exact lsc_line_dyadic
  · exact lsc_line_weighted

/-! ### Proof of `tail_sum` (L7_11): Euler products and the tail. -/

theorem hasProd_sqfree (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hsq : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0)
    (hsum : Summable (fun n => ‖f n‖)) :
    HasProd (fun p : Nat.Primes => 1 + f p) (∑' n, f n) := by
  have h := EulerProduct.eulerProduct_hasProd hf1 hmul hsum hf0
  have hloc : (fun p : Nat.Primes => ∑' e, f ((p : ℕ) ^ e)) = (fun p : Nat.Primes => 1 + f p) := by
    funext p
    rw [tsum_eq_sum (s := Finset.range 2)]
    · simp [Finset.sum_range_succ, hf1]
    · intro e he
      simp only [Finset.mem_range, not_lt] at he
      exact hsq p e p.2 he
  rwa [hloc] at h

theorem prodPF_mul (g : ℕ → ℝ) {m n : ℕ} (h : Nat.Coprime m n) :
    ∏ p ∈ (m * n).primeFactors, g p = (∏ p ∈ m.primeFactors, g p) * ∏ p ∈ n.primeFactors, g p := by
  rw [Nat.Coprime.primeFactors_mul h, Finset.prod_union h.disjoint_primeFactors]

theorem moebius_mul_real {m n : ℕ} (h : Nat.Coprime m n) :
    ((ArithmeticFunction.moebius (m * n) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius m : ℤ) : ℝ) * ((ArithmeticFunction.moebius n : ℤ) : ℝ) := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]; push_cast; ring

theorem moebius_prime_pow_real {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    ((ArithmeticFunction.moebius (p ^ k) : ℤ) : ℝ) = 0 := by
  rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]; simp

theorem abs_moebius_real (e : ℕ) : |((ArithmeticFunction.moebius e : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem prod_inv_le_one (S : Finset ℕ) (g : ℕ → ℝ) (hg : ∀ p ∈ S, 1 ≤ g p) :
    0 ≤ ∏ p ∈ S, (g p)⁻¹ ∧ ∏ p ∈ S, (g p)⁻¹ ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun p hp => inv_nonneg.mpr (by linarith [hg p hp]))
  · exact Finset.prod_le_one (fun p hp => inv_nonneg.mpr (by linarith [hg p hp]))
      (fun p hp => inv_le_one_of_one_le₀ (hg p hp))

/-- `μ(d)/d²`. -/
def m2f (e : ℕ) : ℝ := ((ArithmeticFunction.moebius e : ℤ) : ℝ) / (e : ℝ) ^ 2

/-- plain kind: `μ(e)/e³ ∏_{p|e} (1 + 1/p − 1/p²)⁻¹`. -/
def bPl (e : ℕ) : ℝ := ((ArithmeticFunction.moebius e : ℤ) : ℝ) / (e : ℝ) ^ 3 *
  ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹

/-- `q/φ` kind: `μ(e)/(φ(e) e²) ∏_{p|e} (1 + 1/p)⁻¹`. -/
def bQp (e : ℕ) : ℝ := ((ArithmeticFunction.moebius e : ℤ) : ℝ) / (Nat.totient e : ℝ) / (e : ℝ) ^ 2 *
  ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹

theorem summable_inv_sq : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

theorem one_le_plfac (p : ℕ) (hp : p ∈ Nat.primeFactors p ∨ True) (hp2 : 2 ≤ p) :
    1 ≤ 1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have : 1 / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

theorem abs_m2f_le (e : ℕ) : |m2f e| ≤ 1 / (e : ℝ) ^ 2 := by
  unfold m2f
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2)]
  exact div_le_div_of_nonneg_right (abs_moebius_real e) (by positivity)

theorem abs_bPl_le (e : ℕ) : |bPl e| ≤ 1 / (e : ℝ) ^ 2 := by
  unfold bPl
  obtain ⟨h0, h1⟩ := prod_inv_le_one e.primeFactors (fun p => 1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)
    (fun p hp => one_le_plfac p (Or.inr trivial) (Nat.prime_of_mem_primeFactors hp).two_le)
  rw [abs_mul, abs_of_nonneg h0, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 3)]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / (e : ℝ) ^ 3 * ∏ p ∈ e.primeFactors,
        (1 + 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2)⁻¹ ≤ 1 / (e : ℝ) ^ 3 * 1 := by
        apply mul_le_mul (div_le_div_of_nonneg_right (abs_moebius_real e) (by positivity)) h1 h0
        positivity
    _ ≤ 1 / (e : ℝ) ^ 2 := by
        rw [mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_le_pow_right₀ heR (show 2 ≤ 3 by norm_num)]

theorem abs_bQp_le (e : ℕ) : |bQp e| ≤ 1 / (e : ℝ) ^ 2 := by
  unfold bQp
  obtain ⟨h0, h1⟩ := prod_inv_le_one e.primeFactors (fun p => 1 + 1 / (p : ℝ))
    (fun p _ => by have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
                   linarith)
  rw [abs_mul, abs_of_nonneg h0, abs_div, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient e : ℝ))]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hφ : (1 : ℝ) ≤ Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he
  calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) / (e : ℝ) ^ 2 *
        ∏ p ∈ e.primeFactors, (1 + 1 / (p : ℝ))⁻¹ ≤ 1 / (e : ℝ) ^ 2 * 1 := by
        apply mul_le_mul _ h1 h0 (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [div_le_one (by linarith)]
        linarith [abs_moebius_real e]
    _ = 1 / (e : ℝ) ^ 2 := mul_one _

theorem summable_of_inv_sq {f : ℕ → ℝ} (hf : ∀ e, |f e| ≤ 1 / (e : ℝ) ^ 2) : Summable (fun n => ‖f n‖) :=
  Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hf n)
    summable_inv_sq

theorem hasProd_m2f : HasProd (fun p : Nat.Primes => 1 + m2f p) (6 / Real.pi ^ 2) := by
  have h := hasProd_sqfree m2f (by simp [m2f]) (by simp [m2f])
    (fun {m n} hmn => by unfold m2f; rw [moebius_mul_real hmn]; push_cast; ring)
    (fun p k hp hk => by unfold m2f; rw [moebius_prime_pow_real hp hk, zero_div])
    (summable_of_inv_sq abs_m2f_le)
  have hs : ∑' n, m2f n = 6 / Real.pi ^ 2 := by
    have := ZetaQ.Normalisation.N2.hasSum_mu_sq
    exact this.tsum_eq
  rwa [hs] at h

theorem hasProd_bPl : HasProd (fun p : Nat.Primes => 1 + bPl p) (∑' n, bPl n) :=
  hasProd_sqfree bPl (by simp [bPl]) (by simp [bPl])
    (fun {m n} hmn => by
      unfold bPl
      rw [moebius_mul_real hmn, prodPF_mul _ hmn]; push_cast; ring)
    (fun p k hp hk => by unfold bPl; rw [moebius_prime_pow_real hp hk, zero_div, zero_mul])
    (summable_of_inv_sq abs_bPl_le)

theorem hasProd_bQp : HasProd (fun p : Nat.Primes => 1 + bQp p) (∑' n, bQp n) :=
  hasProd_sqfree bQp (by simp [bQp]) (by simp [bQp])
    (fun {m n} hmn => by
      unfold bQp
      rw [moebius_mul_real hmn, prodPF_mul _ hmn, Nat.totient_mul hmn]; push_cast; ring)
    (fun p k hp hk => by unfold bQp; rw [moebius_prime_pow_real hp hk, zero_div, zero_div, zero_mul])
    (summable_of_inv_sq abs_bQp_le)

theorem Pi0_multipliable :
    Multipliable (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)) := by
  have hs : Summable (fun n : ℕ => 3 * (1 / (n : ℝ) ^ 2)) := summable_inv_sq.mul_left 3
  have hsP : Summable (fun p : Nat.Primes => 3 * (1 / ((p : ℕ) : ℝ) ^ 2)) :=
    hs.comp_injective Subtype.val_injective
  have hnorm : Summable (fun p : Nat.Primes =>
      ‖(-(2 / ((p : ℕ) : ℝ) ^ 2) + 1 / ((p : ℕ) : ℝ) ^ 3)‖) := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hsP
    have hp : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
    have h3 : 1 / ((p : ℕ) : ℝ) ^ 3 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity); nlinarith
    have h3' : 0 ≤ 1 / ((p : ℕ) : ℝ) ^ 3 := by positivity
    have hq2 : 0 ≤ 1 / ((p : ℕ) : ℝ) ^ 2 := by positivity
    have e2 : 2 / ((p : ℕ) : ℝ) ^ 2 = 2 * (1 / ((p : ℕ) : ℝ) ^ 2) := by ring
    rw [Real.norm_eq_abs, abs_le, e2]
    constructor <;> linarith
  have hm := multipliable_one_add_of_summable hnorm
  have e : (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3))
      = (fun p : Nat.Primes => 1 + (-(2 / ((p : ℕ) : ℝ) ^ 2) + 1 / ((p : ℕ) : ℝ) ^ 3)) := by
    funext p; ring
  rw [e]; exact hm

theorem local_plain_identity (x : ℝ) (hx : 2 ≤ x) :
    (1 - 2 / x ^ 2 + 1 / x ^ 3) * (1 + -1 / x ^ 3 * (1 + 1 / x - 1 / x ^ 2)⁻¹)
      = (1 + -1 / x ^ 2) * (1 + -1 / x ^ 2) := by
  have hx0 : x ≠ 0 := by linarith
  have hq : x ^ 2 + x - 1 ≠ 0 := by nlinarith
  have ep : (1 + 1 / x - 1 / x ^ 2)⁻¹ = x ^ 2 / (x ^ 2 + x - 1) := by
    rw [show 1 + 1 / x - 1 / x ^ 2 = (x ^ 2 + x - 1) / x ^ 2 by field_simp, inv_div]
  rw [ep]
  field_simp
  have hDi : (-1 + x + x ^ 2) * (-1 + x + x ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (by nlinarith)
  linear_combination (1 - x) * hDi

theorem tsum_bPl : Pi0plain * ∑' n, bPl n = (6 / Real.pi ^ 2) ^ 2 := by
  have h1 : HasProd (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3)) Pi0plain :=
    Pi0_multipliable.hasProd
  have h12 := h1.mul hasProd_bPl
  have h33 := hasProd_m2f.mul hasProd_m2f
  have hfun : (fun p : Nat.Primes => (1 - 2 / ((p : ℕ) : ℝ) ^ 2 + 1 / ((p : ℕ) : ℝ) ^ 3) * (1 + bPl p))
      = (fun p : Nat.Primes => (1 + m2f p) * (1 + m2f p)) := by
    funext p
    have hp := p.2
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith
    have hq : (1 + 1 / ((p : ℕ) : ℝ) - 1 / ((p : ℕ) : ℝ) ^ 2) ≠ 0 := by
      have := one_le_plfac (p : ℕ) (Or.inr trivial) hp.two_le; linarith
    have hq2 : -1 + ((p : ℕ) : ℝ) + ((p : ℕ) : ℝ) ^ 2 ≠ 0 := by nlinarith
    have hq3 : ((p : ℕ) : ℝ) ^ 2 + ((p : ℕ) : ℝ) - 1 ≠ 0 := by nlinarith
    simp only [bPl, m2f, ArithmeticFunction.moebius_apply_prime hp, Nat.Prime.primeFactors hp,
      Finset.prod_singleton]
    push_cast
    exact local_plain_identity _ hp2
  rw [hfun] at h12
  rw [HasProd.unique h12 h33]
  ring

theorem tsum_bQp : 6 / Real.pi ^ 2 * ∑' n, bQp n = Sconst := by
  have h12 := hasProd_m2f.mul hasProd_bQp
  have hS : HasProd (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2 - 1 / ((p : ℕ) : ℝ) ^ 3)) Sconst :=
    Sconst_multipliable.hasProd
  have hfun : (fun p : Nat.Primes => (1 + m2f p) * (1 + bQp p))
      = (fun p : Nat.Primes => (1 - 1 / ((p : ℕ) : ℝ) ^ 2 - 1 / ((p : ℕ) : ℝ) ^ 3)) := by
    funext p
    have hp := p.2
    have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp.two_le
    have hp0 : ((p : ℕ) : ℝ) ≠ 0 := by linarith
    have hp1 : ((p : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    have hq : (1 + 1 / ((p : ℕ) : ℝ)) ≠ 0 := by
      have : (0 : ℝ) < 1 / ((p : ℕ) : ℝ) := by positivity
      linarith
    have hpp1 : ((p : ℕ) : ℝ) + 1 ≠ 0 := by linarith
    simp only [bQp, m2f, ArithmeticFunction.moebius_apply_prime hp, Nat.Prime.primeFactors hp,
      Finset.prod_singleton, Nat.totient_prime hp]
    rw [Nat.cast_sub hp.one_le]
    push_cast
    field_simp
    ring
  rw [hfun] at h12
  exact HasProd.unique h12 hS

/-- the `e`-summand `c_e Π(e)/e²` equals `Π₀·b(e)` (plain) or `(6/π²)·b'(e)` (`q/φ`). -/
theorem summand_eq (k : FKind) (e : ℕ) :
    cE k e * PiE k e / (e : ℝ) ^ 2
      = (match k with | .plain => Pi0plain * bPl e | .qphi => 6 / Real.pi ^ 2 * bQp e) := by
  cases k
  · simp only [cE, PiE, bPl]; ring
  · simp only [cE, PiE, bQp]; ring

theorem inv_sq_tail_P (L M : ℕ) (hL : 1 ≤ L) : ∑ b ∈ Finset.Ioc L M, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / L := by
  have key : ∀ k : ℕ, ∑ b ∈ Finset.Ioc L (L + k), (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / L - 1 / ((L + k : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show L + (k + 1) = (L + k) + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
      have hx : (1 : ℝ) ≤ ((L + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L + k)
      set x : ℝ := ((L + k : ℕ) : ℝ) with hxdef
      have hc : (((L + k + 1 : ℕ)) : ℝ) = x + 1 := by rw [hxdef]; push_cast; ring
      rw [hc]
      have h2 : 1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
        have e : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by field_simp; ring
        rw [e]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      linarith
  by_cases hM : L ≤ M
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hM
    have h := key k
    have : (0 : ℝ) ≤ 1 / ((L + k : ℕ) : ℝ) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity

/-- generic tail: if `Σ a = A` and `|a(e)| ≤ K/e²`, then `|Σ_{e≤N} a(e) − A| ≤ K/N`. -/
theorem tail_generic (a : ℕ → ℝ) (A K : ℝ) (hA : HasSum a A) (hK : ∀ e, |a e| ≤ K / (e : ℝ) ^ 2)
    (N : ℕ) (hN : 1 ≤ N) : |∑ e ∈ Finset.Icc 1 N, a e - A| ≤ K / N := by
  have hK0 : 0 ≤ K := by
    have := hK 1; simp at this; linarith [abs_nonneg (a 1)]
  have ha0 : a 0 = 0 := by
    have := hK 0; simp at this; exact this
  have hS := hA.tendsto_sum_nat
  have key : ∀ M ≥ N, |∑ e ∈ Finset.range (M + 1), a e - ∑ e ∈ Finset.Icc 1 N, a e| ≤ K / N := by
    intro M hM
    have e2 := Finset.sum_Ioc_consecutive a (Nat.zero_le N) hM
    have i1 : Finset.range (M + 1) = insert 0 (Finset.Ioc 0 M) := by
      ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
    have i2 : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e1 : ∑ e ∈ Finset.range (M + 1), a e = ∑ e ∈ Finset.Ioc 0 M, a e := by
      rw [i1, Finset.sum_insert (by simp), ha0, zero_add]
    rw [e1, i2, ← e2, add_sub_cancel_left]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e ∈ Finset.Ioc N M, |a e| ≤ ∑ e ∈ Finset.Ioc N M, K * (1 / (e : ℝ) ^ 2) :=
          Finset.sum_le_sum (fun e _ => by rw [mul_one_div]; exact hK e)
      _ = K * ∑ e ∈ Finset.Ioc N M, 1 / (e : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K * (1 / N) := mul_le_mul_of_nonneg_left (inv_sq_tail_P N M hN) hK0
      _ = K / N := by ring
  have hlim : Filter.Tendsto
      (fun M : ℕ => |∑ e ∈ Finset.range (M + 1), a e - ∑ e ∈ Finset.Icc 1 N, a e|)
      Filter.atTop (nhds |A - ∑ e ∈ Finset.Icc 1 N, a e|) :=
    ((hS.comp (Filter.tendsto_add_atTop_nat 1)).sub_const _).abs
  have := le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨N, key⟩)
  rw [abs_sub_comm]
  exact this

theorem gbar_eq (F : Fam) : gbar F = F.W1 * (match F.kind with
    | .plain => Pi0plain * ∑' n, bPl n | .qphi => 6 / Real.pi ^ 2 * ∑' n, bQp n) := by
  cases F <;> simp only [gbar, Fam.kind, Fam.W1]
  · rw [tsum_bPl]; ring
  · rw [tsum_bPl]; ring
  · rw [tsum_bQp]

theorem hasSum_summand (k : FKind) :
    HasSum (fun e : ℕ => cE k e * PiE k e / (e : ℝ) ^ 2)
      (match k with | .plain => Pi0plain * ∑' n, bPl n | .qphi => 6 / Real.pi ^ 2 * ∑' n, bQp n) := by
  have e : (fun e : ℕ => cE k e * PiE k e / (e : ℝ) ^ 2)
      = (fun e : ℕ => (match k with | .plain => Pi0plain * bPl e | .qphi => 6 / Real.pi ^ 2 * bQp e)) := by
    funext e; exact summand_eq k e
  rw [e]
  cases k
  · exact ((summable_of_inv_sq abs_bPl_le).of_norm.hasSum).mul_left Pi0plain
  · exact ((summable_of_inv_sq abs_bQp_le).of_norm.hasSum).mul_left (6 / Real.pi ^ 2)

theorem abs_summand_le (k : FKind) (e : ℕ) :
    |cE k e * PiE k e / (e : ℝ) ^ 2| ≤ (|Pi0plain| + 1) / (e : ℝ) ^ 2 := by
  rw [summand_eq]
  have hpi : (6 : ℝ) / Real.pi ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  cases k
  · simp only
    rw [abs_mul]
    calc |Pi0plain| * |bPl e| ≤ |Pi0plain| * (1 / (e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_bPl_le e) (abs_nonneg _)
      _ ≤ (|Pi0plain| + 1) * (1 / (e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (|Pi0plain| + 1) / (e : ℝ) ^ 2 := by ring
  · simp only
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 6 / Real.pi ^ 2)]
    calc 6 / Real.pi ^ 2 * |bQp e| ≤ 1 * (1 / (e : ℝ) ^ 2) :=
          mul_le_mul hpi (abs_bQp_le e) (abs_nonneg _) (by norm_num)
      _ ≤ (|Pi0plain| + 1) * (1 / (e : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg Pi0plain]) (by positivity)
      _ = (|Pi0plain| + 1) / (e : ℝ) ^ 2 := by ring

/-- **Sub-node `tail_sum` (PROVED).** The `e`-sum of the main terms and its tail. -/
theorem tail_sum (F : Fam) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 1 ≤ v →
    |F.W1 * ∑ e ∈ Finset.Icc 1 ⌊v⌋₊, cE F.kind e * PiE F.kind e / (e : ℝ) ^ 2 - gbar F| ≤ C / v := by
  have hW : 0 < F.W1 := by cases F <;> simp only [Fam.W1] <;> norm_num
  refine ⟨F.W1 * (2 * (|Pi0plain| + 1)), by positivity, fun v hv => ?_⟩
  set N := ⌊v⌋₊ with hN
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hv)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hvN : v < N + 1 := Nat.lt_floor_add_one v
  have ht := tail_generic _ _ (|Pi0plain| + 1) (hasSum_summand F.kind) (abs_summand_le F.kind) N hN1
  rw [gbar_eq, ← mul_sub, abs_mul, abs_of_pos hW]
  have hv0 : 0 < v := by linarith
  have h2 : (|Pi0plain| + 1) / (N : ℝ) ≤ 2 * (|Pi0plain| + 1) / v := by
    rw [div_le_div_iff₀ (by positivity) hv0]
    have : 0 ≤ |Pi0plain| + 1 := by positivity
    nlinarith
  calc F.W1 * |∑ e ∈ Finset.Icc 1 N, cE F.kind e * PiE F.kind e / (e : ℝ) ^ 2 -
        (match F.kind with | .plain => Pi0plain * ∑' n, bPl n | .qphi => 6 / Real.pi ^ 2 * ∑' n, bQp n)|
      ≤ F.W1 * ((|Pi0plain| + 1) / N) := mul_le_mul_of_nonneg_left ht hW.le
    _ ≤ F.W1 * (2 * (|Pi0plain| + 1) / v) := mul_le_mul_of_nonneg_left h2 hW.le
    _ = F.W1 * (2 * (|Pi0plain| + 1)) / v := by ring

/-- **Sub-node (PROVED).** `Σ_{e≤N} |c_e| τ(e)/e ≤ C`. -/
theorem sum_cE_tau (F : Fam) : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    ∑ e ∈ Finset.Icc 1 N, |cE F.kind e| * (e.divisors.card : ℝ) / e ≤ C := by
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ 2 with hZ
  refine ⟨(Z ^ 2) ^ 2 + Z ^ 2, by positivity, fun N => ?_⟩
  have hZ2 : 0 ≤ Z ^ 2 := by positivity
  have hmu : ∀ e : ℕ, |((ArithmeticFunction.moebius e : ℤ) : ℝ)| ≤ 1 := fun e => by
    rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  cases hk : F.kind
  · have h1 : ∀ e ∈ Finset.Icc 1 N, |cE FKind.plain e| * (e.divisors.card : ℝ) / e
        ≤ (e.divisors.card : ℝ) / (e : ℝ) ^ 2 := by
      intro e he
      have heR : (0 : ℝ) < e := by exact_mod_cast (Finset.mem_Icc.mp he).1
      simp only [cE]
      rw [abs_div, abs_of_pos heR]
      have hτ : (0 : ℝ) ≤ (e.divisors.card : ℝ) := by positivity
      calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / e * (e.divisors.card : ℝ) / e
          ≤ 1 / e * (e.divisors.card : ℝ) / e := by
            apply div_le_div_of_nonneg_right _ heR.le
            exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hmu e) heR.le) hτ
        _ = (e.divisors.card : ℝ) / (e : ℝ) ^ 2 := by field_simp
    refine (Finset.sum_le_sum h1).trans ((ZetaShell.MuSqPhi.sum_tau_div_sq_le N).trans ?_)
    nlinarith [sq_nonneg (Z ^ 2)]
  · have h1 : ∀ e ∈ Finset.Icc 1 N, |cE FKind.qphi e| * (e.divisors.card : ℝ) / e
        ≤ (e.divisors.card : ℝ) ^ 2 / (e : ℝ) ^ 2 := by
      intro e he
      have he0 : e ≠ 0 := by rw [Finset.mem_Icc] at he; omega
      have heR : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero he0
      have hφ := ZetaShell.MuSqPhi.inv_totient_le e he0
      simp only [cE]
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient e : ℝ))]
      have hτ : (0 : ℝ) ≤ (e.divisors.card : ℝ) := by positivity
      calc |((ArithmeticFunction.moebius e : ℤ) : ℝ)| / (Nat.totient e : ℝ) * (e.divisors.card : ℝ) / e
          ≤ 1 / (Nat.totient e : ℝ) * (e.divisors.card : ℝ) / e := by
            apply div_le_div_of_nonneg_right _ heR.le
            exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hmu e) (by positivity)) hτ
        _ ≤ (e.divisors.card : ℝ) / e * (e.divisors.card : ℝ) / e := by
            apply div_le_div_of_nonneg_right _ heR.le
            exact mul_le_mul_of_nonneg_right hφ hτ
        _ = (e.divisors.card : ℝ) ^ 2 / (e : ℝ) ^ 2 := by field_simp
    refine (Finset.sum_le_sum h1).trans ((ZetaShell.MuSqPhi.sum_tau_sq_div_sq_le N).trans ?_)
    linarith

/-- **A2P (lem:shell-P).** For each family there is `B` with `|g_r(v) − ḡ_w| ≤ B (1 + log v)²/v` for all `r ≥ 1`,
`v ≥ 1`. -/
theorem lemmaP (F : Fam) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℕ, 1 ≤ r → ∀ v : ℝ, 1 ≤ v →
      |gProf F r v - gbar F| ≤ B * (1 + Real.log v) ^ 2 / v := by
  obtain ⟨C1, hC1, h1⟩ := line_sum_asymp F
  obtain ⟨C2, hC2, h2⟩ := tail_sum F
  obtain ⟨C3, hC3, h3⟩ := sum_cE_tau F
  refine ⟨C1 * C3 + C2, by positivity, ?_⟩
  intro r hr v hv
  have hv0 : 0 < v := by linarith
  set N : ℕ := ⌊v⌋₊ with hN
  have hNv : (N : ℝ) ≤ v := Nat.floor_le hv0.le
  have hlogv : 0 ≤ Real.log v := Real.log_nonneg hv
  -- the inner sums
  set S : ℕ → ℝ := fun e => ∑ j ∈ Finset.Icc 1 ⌊v / e⌋₊, (Nat.totient j : ℝ) * Ecoef F.kind r j e *
    F.w ((j : ℝ) / (v / e)) with hS
  have hswap : gProf F r v = (v ^ 2)⁻¹ * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * S e := by
    unfold gProf
    try rw [← hN]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heR : (0 : ℝ) < e := by exact_mod_cast he1
    have heN : e ≤ N := (Finset.mem_Icc.mp he).2
    have hfl : ⌊v / e⌋₊ ≤ N := Nat.floor_le_floor (div_le_self hv0.le (by exact_mod_cast he1))
    simp only [hS, Finset.mul_sum]
    have hsub : Finset.Icc 1 ⌊v / e⌋₊ ⊆ Finset.Icc 1 N := by
      intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
    have h0 : ∀ j ∈ Finset.Icc 1 N, j ∉ Finset.Icc 1 ⌊v / e⌋₊ →
        cE F.kind e * ((Nat.totient j : ℝ) * Ecoef F.kind r j e * F.w ((j : ℝ) / (v / e))) = 0 := by
      intro j hj hn
      rw [Finset.mem_Icc] at hj
      have hjv : v / e < j := by
        by_contra hcon
        push_neg at hcon
        exact hn (Finset.mem_Icc.mpr ⟨hj.1, Nat.le_floor hcon⟩)
      have hw : F.w ((j : ℝ) / (v / e)) = 0 := by
        apply F.w_zero_gt_one_P
        rw [lt_div_iff₀ (by positivity)]
        linarith
      rw [hw]; ring
    rw [Finset.sum_subset hsub h0]
    apply Finset.sum_congr rfl
    intro j _
    have harg : (j : ℝ) / (v / e) = (j : ℝ) * e / v := by field_simp
    rw [harg]; ring
  -- bound each line sum
  have hS1 : ∀ e ∈ Finset.Icc 1 N, |S e - (v / e) ^ 2 * F.W1 * PiE F.kind e|
      ≤ C1 * (e.divisors.card : ℝ) * ((v / e) * (1 + Real.log v) ^ 2) := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have heR : (1 : ℝ) ≤ e := by exact_mod_cast he1
    have heN : (e : ℝ) ≤ v := le_trans (by exact_mod_cast (Finset.mem_Icc.mp he).2) hNv
    have hy1 : 1 ≤ v / e := by rw [le_div_iff₀ (by linarith)]; linarith
    have hyv : v / e ≤ v := div_le_self hv0.le heR
    refine (h1 r hr e he1 (v / e) hy1).trans ?_
    have hly : Real.log (v / e) ≤ Real.log v := Real.log_le_log (by linarith) hyv
    have hly0 : 0 ≤ Real.log (v / e) := Real.log_nonneg hy1
    have hsq : (1 + Real.log (v / e)) ^ 2 ≤ (1 + Real.log v) ^ 2 := by nlinarith
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hmain : (v ^ 2)⁻¹ * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * ((v / e) ^ 2 * F.W1 * PiE F.kind e)
      = F.W1 * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * PiE F.kind e / (e : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have heR : (0 : ℝ) < e := by exact_mod_cast (Finset.mem_Icc.mp he).1
    field_simp
  have hsplit : gProf F r v - gbar F
      = (v ^ 2)⁻¹ * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * (S e - (v / e) ^ 2 * F.W1 * PiE F.kind e)
        + (F.W1 * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * PiE F.kind e / (e : ℝ) ^ 2 - gbar F) := by
    rw [hswap, ← hmain]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  have hA : |(v ^ 2)⁻¹ * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * (S e - (v / e) ^ 2 * F.W1 * PiE F.kind e)|
      ≤ C1 * C3 * (1 + Real.log v) ^ 2 / v := by
    rw [abs_mul, abs_of_pos (by positivity)]
    have hb : |∑ e ∈ Finset.Icc 1 N, cE F.kind e * (S e - (v / e) ^ 2 * F.W1 * PiE F.kind e)|
        ≤ C1 * v * (1 + Real.log v) ^ 2 * ∑ e ∈ Finset.Icc 1 N, |cE F.kind e| * (e.divisors.card : ℝ) / e := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      have heR : (0 : ℝ) < e := by exact_mod_cast (Finset.mem_Icc.mp he).1
      rw [abs_mul]
      calc |cE F.kind e| * |S e - (v / e) ^ 2 * F.W1 * PiE F.kind e|
          ≤ |cE F.kind e| * (C1 * (e.divisors.card : ℝ) * ((v / e) * (1 + Real.log v) ^ 2)) :=
            mul_le_mul_of_nonneg_left (hS1 e he) (abs_nonneg _)
        _ = C1 * v * (1 + Real.log v) ^ 2 * (|cE F.kind e| * (e.divisors.card : ℝ) / e) := by
            field_simp
    have hc3 := h3 N
    have hL : 0 ≤ C1 * v * (1 + Real.log v) ^ 2 := by positivity
    calc (v ^ 2)⁻¹ * |∑ e ∈ Finset.Icc 1 N, cE F.kind e * (S e - (v / e) ^ 2 * F.W1 * PiE F.kind e)|
        ≤ (v ^ 2)⁻¹ * (C1 * v * (1 + Real.log v) ^ 2 * C3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hb.trans (mul_le_mul_of_nonneg_left hc3 hL)
      _ = C1 * C3 * (1 + Real.log v) ^ 2 / v := by field_simp
  have hB : |F.W1 * ∑ e ∈ Finset.Icc 1 N, cE F.kind e * PiE F.kind e / (e : ℝ) ^ 2 - gbar F|
      ≤ C2 * (1 + Real.log v) ^ 2 / v := by
    refine (h2 v hv).trans ?_
    rw [div_le_div_iff_of_pos_right hv0]
    have : (1 : ℝ) ≤ (1 + Real.log v) ^ 2 := by nlinarith
    nlinarith
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ C1 * C3 * (1 + Real.log v) ^ 2 / v + C2 * (1 + Real.log v) ^ 2 / v := add_le_add hA hB
    _ = (C1 * C3 + C2) * (1 + Real.log v) ^ 2 / v := by ring

/-! ### Proved local identities (proof of Lemma P, step (iii), and the evaluation) -/

/-- step (iii), `p ∤ r`: `(1 + λ/p)(1 + ν/p) = (1 − 1/p)(1 + (1+λ)/p)` with `ν = (1 − 1/p)/(1 + λ/p) − 1`. -/
theorem euler_factor_pnr (p l : ℝ) (hp : p ≠ 0) (hl : 1 + l / p ≠ 0) :
    (1 + l / p) * (1 + ((1 - 1 / p) / (1 + l / p) - 1) / p) = (1 - 1 / p) * (1 + (1 + l) / p) := by
  have hpl : p + l ≠ 0 := by
    intro h
    apply hl
    rw [show l = -p by linarith, neg_div, div_self hp]
    ring
  field_simp
  ring

/-- step (iii), `p ∣ r`: `1 + ν/p = (1 − 1/p)(1 + h/p)` with `ν = (1 − 1/p)h − 1`. -/
theorem euler_factor_pr (p h : ℝ) (hp : p ≠ 0) :
    1 + ((1 - 1 / p) * h - 1) / p = (1 - 1 / p) * (1 + h / p) := by
  field_simp
  ring

/-- evaluation, plain kind, one prime: `Π_p(e∤) + (μ(p)/p³)·Π_p(e|) = (1 − p⁻²)²`. -/
theorem euler_eval_plain (p : ℝ) (hp : p ≠ 0) :
    (1 - 1 / p) * (1 + (1 - 1 / p) / p) + (-1 / p ^ 3) * ((1 - 1 / p) * (1 + 0 / p))
      = (1 - 1 / p ^ 2) ^ 2 := by
  field_simp
  ring

/-- evaluation, `q/φ` kind, one prime: `Π_p(e∤) + (μ(p)/(φ(p)p²))·Π_p(e|) = 1 − p⁻² − p⁻³`. -/
theorem euler_eval_qphi (p : ℝ) (hp : p ≠ 0) (hp1 : p - 1 ≠ 0) :
    (1 - 1 / p) * (1 + 1 / p) + (-1 / ((p - 1) * p ^ 2)) * ((1 - 1 / p) * (1 + 0 / p))
      = 1 - 1 / p ^ 2 - 1 / p ^ 3 := by
  field_simp
  ring

end TrackF
end ZetaShell

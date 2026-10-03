/-
lean_work/L0_4/Interfaces.lean — the decoupling interfaces of LEAN_PLAN §1.4 for the ζ follow-up (L0_4, 28 Sep 2026).

  * `GramData`   — one height T, the paper's §6 layer (`P1`, `Qp`, `Gt = P1 + Qp`, counts, AF1/AF2 and the count
                   inequality) PLUS what the stability route (lem:zeta-stab, thm:zeta-G) needs beyond the paper: the
                   factor `V` of `P1` (columns = normalised vectors of the simple on-line zeros), their normalised
                   ordinates `x`, the true-window kernel `k` and the grid-truncation matrix `Etr` with
                   `Vᵀ V = (k(x_i − x_j)) − Etr` (Poisson, eq:zeta-poisson), and the span `Λ`.
  * `ZeroFrame`  — one height T, the finer zero-side data that the all-marks theorems (thm:sigd-Sigma/D) and
                   cor:oll-SC consume: ALL distinct on-line zeros with multiplicities, their vectors and ordinates, the
                   off-line block `Qoff` with its inertia, and the counts. `GramData` is derived from it (node K0).
  * `GramFamily`, `FrameFamily` — the asymptotic wrappers (AF3, AF4, window, span, truncation, kernel closeness),
                   in the tree's little-o idiom (`=o[atTop] N`, as `err_isLittleO`/`eps_form_of_isLittleO` in
                   Zeta23/Assembly.lean consume it; `EvBound` rates convert by node T1).
  * `LocalCert`, `LocalCertAM`, `MajorantCert` and the four headline statements live in the Mathlib-only file
    `ChallengeZetaS.lean` (namespace `ZetaS`), imported here.
  * The constants of thm:zeta-G (`PhiM`, `stabConst`) and of thm:sigd-Sigma/D (`sigmaConst`, `distConst`).

Compile (from $LEAN): LEAN_PATH=<this folder>/olean lake env lean --root=<this folder> Interfaces.lean
The file contains no `sorry`.
-/
import ZetaS.ChallengeZetaS
import Zeta23.LinAlg.RankTrace

noncomputable section

open scoped BigOperators
open Matrix Filter Topology Asymptotics Finset

namespace ZetaS

/-! ## 1. Kernels on point sets -/

/-- The kernel matrix `(k(x_i − x_j))_{i,j}` of a point set. -/
def kerMat (k : ℝ → ℝ) {n : ℕ} (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => k (x i - x j)

/-- `k` is a positive-definite kernel on `ℝ` (Bochner sense, finite point sets): every kernel matrix is PSD.
Holds for `k_φ` and `k_ψ` (Fourier transforms of nonnegative densities). -/
def IsPosDefKernel (k : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ), (kerMat k x).PosSemidef

/-! ## 2. `GramData`: one height, the stability route -/

/-- **`GramData`** — the data and facts at one height `T` that the algebraic side of the stability route consumes.

Paper layer (AF §6; draft ssec:zeta-setting, sec_zeta.tex l.188–204 and prop:zeta-AF l.206–214):
`Gt = Ĝ = P1 + Qp` real symmetric `d × d` (d = ⌊LT/2π⌋, bilinear transpose, eq:zeta-Ghat), `P1 ⪰ 0` the simple
on-line part, `rank P1 ≤ s1`, (AF1) `tr P1 ≤ s1`, (AF2) `n₊(Qp) ≤ s2 + p`, and `s1 + 2s2 + 2p ≤ N(I′) =: Nw`.

Stability layer (cor:zeta-stab l.271–290, "What tr Ψ(M°) is" l.292–311, lem:zeta-transfer l.461–486):
`P1 = V Vᵀ` with `V ∈ ℝ^{d × s1}`, column `i` = `u_ρ = (aL²)^{−1/2} v_ρ` for the `i`-th simple on-line zero in
increasing order of ordinate; `x i = γ_ρ L/2π` its normalised ordinate; `k` the true-window kernel `k_φ` at this
height; `Etr = Ê` the Gram matrix of the off-grid lattice points (`Ê ⪰ 0`), so that
`M° = Vᵀ V = (k(x_i − x_j)) − Ê` (eq:zeta-poisson); all ordinates lie in an interval of length `Λ = |I′|L/2π`. -/
structure GramData where
  /-- grid size `d = ⌊LT/2π⌋`. -/
  d : ℕ
  P1 : Matrix (Fin d) (Fin d) ℝ
  Qp : Matrix (Fin d) (Fin d) ℝ
  /-- simple on-line zeros with `γ ∈ I′`. -/
  s1 : ℕ
  /-- distinct multiple on-line zeros with `γ ∈ I′`. -/
  s2 : ℕ
  /-- off-line pairs `{ρ, 1 − ρ̄}` with `Re γ ∈ I′`. -/
  p : ℕ
  /-- `N(I′)`, with multiplicity. -/
  Nw : ℕ
  P1_psd : P1.PosSemidef
  Qp_herm : Qp.IsHermitian
  rank_P1 : P1.rank ≤ s1
  /-- (AF1) `tr P1 ≤ s1`. -/
  tr_P1 : RHLinalg.rtrace P1 ≤ s1
  /-- (AF2) `n₊(Qp) ≤ s2 + p`. -/
  nplus_Qp : RHLinalg.posIndex Qp_herm ≤ s2 + p
  count : s1 + 2 * s2 + 2 * p ≤ Nw
  -- stability layer
  V : Matrix (Fin d) (Fin s1) ℝ
  P1_eq : P1 = V * Vᵀ
  x : Fin s1 → ℝ
  x_mono : StrictMono x
  k : ℝ → ℝ
  k_zero : k 0 = 1
  k_even : ∀ t, k (-t) = k t
  k_posDef : IsPosDefKernel k
  Etr : Matrix (Fin s1) (Fin s1) ℝ
  Etr_psd : Etr.PosSemidef
  gram_eq : Vᵀ * V = kerMat k x - Etr
  Λ : ℝ
  Λ_nonneg : 0 ≤ Λ
  x_span : ∀ i j, x j - x i ≤ Λ

namespace GramData

/-- `Ĝ = P1 + Qp`. -/
def Gt (D : GramData) : Matrix (Fin D.d) (Fin D.d) ℝ := D.P1 + D.Qp

/-- `M° = Vᵀ V`, the Gram matrix of the simple on-line zeros (cor:zeta-stab). -/
def Mcirc (D : GramData) : Matrix (Fin D.s1) (Fin D.s1) ℝ := D.Vᵀ * D.V

end GramData

/-! ## 3. `ZeroFrame`: one height, all on-line zeros (all-marks route, simple-or-critical) -/

/-- **`ZeroFrame`** — the zero-side data at one height `T` in the frame of eq:zeta-Ghat, as the all-marks
route (ssec:zeta-allmarks, "Removing pairs and heavy zeros" l.1184–1190, lem:sigd-residue l.1088–1101) and
cor:oll-SC (l.675–709) use it.

On-line zeros: `n` distinct zeros with `γ ∈ I′`, in increasing order of ordinate `x`, multiplicities `m i ≥ 1`,
vectors `U`'s columns `u_ρ`, with `Uᵀ U = (k(x_i − x_j)) − Etr`, `Etr ⪰ 0` (lem:sigd-residue (i)–(ii)); the defect
`δ_ρ = Etr ρ ρ` and `d_ρ = 1 − δ_ρ` are derived. Off-line zeros enter only through `Qoff = Σ_π 2m_π(x_πx_πᵀ − y_πy_πᵀ)`,
its inertia (`n₊, n₋ ≤ p`), and the counts `p`, `p1` (simple pairs), `Noff` (with multiplicity); no off-line vector
is evaluated (draft l.1219). `Ĝ = U diag(m) Uᵀ + Qoff`. -/
structure ZeroFrame where
  d : ℕ
  /-- distinct on-line zeros with `γ ∈ I′`. -/
  n : ℕ
  m : Fin n → ℕ
  one_le_m : ∀ i, 1 ≤ m i
  x : Fin n → ℝ
  x_mono : StrictMono x
  U : Matrix (Fin d) (Fin n) ℝ
  k : ℝ → ℝ
  k_zero : k 0 = 1
  k_even : ∀ t, k (-t) = k t
  k_posDef : IsPosDefKernel k
  Etr : Matrix (Fin n) (Fin n) ℝ
  Etr_psd : Etr.PosSemidef
  gram_eq : Uᵀ * U = kerMat k x - Etr
  Qoff : Matrix (Fin d) (Fin d) ℝ
  Qoff_herm : Qoff.IsHermitian
  /-- off-line pairs with `Re γ ∈ I′`, and the simple ones among them. -/
  p : ℕ
  p1 : ℕ
  p1_le : p1 ≤ p
  nplus_off : RHLinalg.posIndex Qoff_herm ≤ p
  nminus_off : RHLinalg.negIndex Qoff_herm ≤ p
  /-- off-line zeros with `Re γ ∈ I′`, with multiplicity: `Noff = 2 Σ_π m_π ≥ 2p1 + 4(p − p1)`. -/
  Noff : ℕ
  Noff_ge : 2 * p1 + 4 * (p - p1) ≤ Noff
  Λ : ℝ
  Λ_nonneg : 0 ≤ Λ
  x_span : ∀ i j, x j - x i ≤ Λ

namespace ZeroFrame

variable (F : ZeroFrame)

/-- `Ĝ = Σ_{on-line} m_ρ u_ρ u_ρᵀ + Qoff`. -/
def Gt : Matrix (Fin F.d) (Fin F.d) ℝ :=
  F.U * Matrix.diagonal (fun i => (F.m i : ℝ)) * F.Uᵀ + F.Qoff

/-- `N(I′) = Σ m_ρ (on-line) + Noff`. -/
def Nw : ℕ := (∑ i, F.m i) + F.Noff

/-- `s_j` for `j = 1, 2`: distinct on-line zeros of multiplicity exactly `j`. -/
def sEq (j : ℕ) : ℕ := #(univ.filter fun i => F.m i = j)

/-- heavy on-line zeros (multiplicity `≥ 3`): distinct count `s_H` and count with multiplicity `N_H`. -/
def sH : ℕ := #(univ.filter fun i => 3 ≤ F.m i)
def NH : ℕ := ∑ i ∈ univ.filter (fun i => 3 ≤ F.m i), F.m i

/-- the defect `δ_ρ = Σ_{l ∉ [0,d)} U_ρ(l)²` (lem:sigd-residue (i)). -/
def delta (i : Fin F.n) : ℝ := F.Etr i i

/-- the window counts of the three statistics (proof of thm:sigd-Sigma/D, l.1379; cor:oll-SC, l.680):
`Nˢ(I′) = s1 + 2p1`, `N^d(I′) = n + 2p`, `N^sc(I′) = N_on + 2p1`. -/
def NsW : ℕ := F.sEq 1 + 2 * F.p1
def NdW : ℕ := F.n + 2 * F.p
def NscW : ℕ := (∑ i, F.m i) + 2 * F.p1

/-- the light on-line zeros (multiplicity 1 or 2) and their Gram matrix `M_L = (√(m m′)⟨u,u′⟩)` (def:sigd-charge). -/
def light : Finset (Fin F.n) := univ.filter fun i => F.m i ≤ 2

def ML : Matrix F.light F.light ℝ :=
  Matrix.of fun i j => Real.sqrt ((F.m i : ℝ) * F.m j) * (F.Uᵀ * F.U) i j

/-- the slack of an on-line set `𝒪` with respect to a count `X` (def:zeta-slack, lem:sigd-onslack):
`X − 2 tr G_𝒪 + ‖G_𝒪‖²`, `G_𝒪 = Σ_{ρ∈𝒪} m_ρ u_ρ u_ρᵀ`. -/
def slackOn (O : Finset (Fin F.n)) (X : ℝ) : ℝ :=
  X - 2 * RHLinalg.rtrace (F.U * Matrix.diagonal (fun i => if i ∈ O then (F.m i : ℝ) else 0) * F.Uᵀ)
    + RHLinalg.frobSq (F.U * Matrix.diagonal (fun i => if i ∈ O then (F.m i : ℝ) else 0) * F.Uᵀ)

end ZeroFrame

/-! ## 4. Asymptotic wrappers -/

/-- **`GramFamily N R kψ`** — `T ↦ GramData` with the analytic inputs of prop:zeta-AF (l.206–214) and
lem:zeta-transfer (l.461–486), as `T → ∞`, against the target count `N T` (for ζ: `Ncount T (2T)`):
(AF3) `tr Ĝ = N + o(N)`; (AF4) `‖Ĝ‖²_F = R·N + o(N)` (the draft's `(R + O(L⁻¹))N` is stronger; only `o(N)` is used);
`N(I′) = N + o(N)`; `Λ ≤ N + o(N)`; `tr Ê = o(N)` (lem:sigd-residue (iv): `Σ δ_ρ ≪ √T log T`); and
`sup_ℝ |k_φ − k_ψ| → 0` (lem:sigd-residue (iii)). -/
structure GramFamily (N : ℝ → ℝ) (R : ℝ) (kψ : ℝ → ℝ) where
  G : ℝ → GramData
  N_nonneg : ∀ᶠ T in atTop, 0 ≤ N T
  N_tendsto : Tendsto N atTop atTop
  trace : (fun T => RHLinalg.rtrace (G T).Gt - N T) =o[atTop] N
  frob : (fun T => RHLinalg.frobSq (G T).Gt - R * N T) =o[atTop] N
  window : (fun T => ((G T).Nw : ℝ) - N T) =o[atTop] N
  span : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop, (G T).Λ ≤ N T + r T
  trunc : (fun T => RHLinalg.rtrace (G T).Etr) =o[atTop] N
  kernel : ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ T in atTop, ∀ t, |(G T).k t - kψ t| ≤ e T

/-- **`FrameFamily N R kψ`** — `T ↦ ZeroFrame` with the same inputs, plus the window domination used by
lem:sigd-env (l.1286–1291: `v_φ ≤ (1 + ε′_T) v_ψ`, i.e. `(1 + ε′_T)k_ψ − k_φ` is a positive-definite kernel),
and the multiplicity bound of lem:sigd-residue (v) in the weighted form `Σ m_ρ δ_ρ = o(N)` (iv). -/
structure FrameFamily (N : ℝ → ℝ) (R : ℝ) (kψ : ℝ → ℝ) where
  F : ℝ → ZeroFrame
  N_nonneg : ∀ᶠ T in atTop, 0 ≤ N T
  N_tendsto : Tendsto N atTop atTop
  trace : (fun T => RHLinalg.rtrace (F T).Gt - N T) =o[atTop] N
  frob : (fun T => RHLinalg.frobSq (F T).Gt - R * N T) =o[atTop] N
  window : (fun T => ((F T).Nw : ℝ) - N T) =o[atTop] N
  span : ∃ r : ℝ → ℝ, r =o[atTop] N ∧ ∀ᶠ T in atTop, (F T).Λ ≤ N T + r T
  defect : (fun T => ∑ i, ((F T).m i : ℝ) * (F T).delta i) =o[atTop] N
  kernel : ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ T in atTop, ∀ t, |(F T).k t - kψ t| ≤ e T
  dominate : ∃ e : ℝ → ℝ, Tendsto e atTop (𝓝 0) ∧
    ∀ᶠ T in atTop, IsPosDefKernel (fun t => (1 + e T) * kψ t - (F T).k t)

/-! ## 5. Spectral functions -/

/-- `Ψ(t)` of eq:zeta-Psi (l.226–229): `(t − 1)²` for `t ≤ 2`, `2t − 3` for `t ≥ 2` (only `t ≥ 0` is ever used). -/
def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

/-- `Ψ_{s,t}(p)` of lem:oll-Ast (l.643): `(p − s)²` for `p ≤ t`, `(t − s)² + 2(t − s)(p − t)` for `p ≥ t`.
`PsiST 1 2 = Psi`. -/
def PsiST (s t p : ℝ) : ℝ := if p ≤ t then (p - s) ^ 2 else (t - s) ^ 2 + 2 * (t - s) * (p - t)

/-- `tr f(A) = Σ_i f(λ_i(A))` for a Hermitian matrix. -/
def trFun {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) : ℝ :=
  ∑ i, f (hA.eigenvalues i)

/-! ## 6. The constants -/

/-- `Φ_m(E)` of lem:zeta-Phi (l.330–338): `E` for `E ≤ m/(m−1)`, else `E − (√((m−1)E/m) − 1)²`. -/
def PhiM (m : ℕ) (E : ℝ) : ℝ :=
  if E ≤ (m : ℝ) / ((m : ℝ) - 1) then E else E - (Real.sqrt (((m : ℝ) - 1) * E / m) - 1) ^ 2

/-- The bound of thm:zeta-G (l.488–494) in the weighted form of lem:zeta-Dprime (l.520–521):
`(H − (B/A)τ)/(1 − B/m)` with `A = c(m − K + 1)`, `B = Φ_m(A)`, `τ = ν(m − K + 1)/m`. -/
def stabConst (H : ℝ) (K : ℕ) (ν c : ℝ) (m : ℕ) : ℝ :=
  let A := c * ((m : ℝ) - K + 1)
  let B := PhiM m A
  let τ := ν * ((m : ℝ) - K + 1) / m
  (H - B / A * τ) / (1 - B / m)

/-- thm:sigd-Sigma (l.1362): `(H + a₂/2 − ν)/(1 − a₁ + a₂/2)`. -/
def sigmaConst (H a₁ a₂ ν : ℝ) : ℝ := (H + a₂ / 2 - ν) / (1 - a₁ + a₂ / 2)

/-- thm:sigd-D (l.1372): `(1 + H + a₂ − a₁ − ν)/(2 − 2a₁ + a₂)`. -/
def distConst (H a₁ a₂ ν : ℝ) : ℝ := (1 + H + a₂ - a₁ - ν) / (2 - 2 * a₁ + a₂)

/-- cor:oll-SC (l.671, l.707): `(2t − 3 + 2S)/(2t − 1)` at `t = 2 + √2`, i.e. `(1 + 2√2 + 2S)/(3 + 2√2)`. -/
def scConst (S : ℝ) : ℝ := (1 + 2 * Real.sqrt 2 + 2 * S) / (3 + 2 * Real.sqrt 2)

/-- `R(ψ)` of eq:zeta-R (l.100–103): `(∫ψ² + ∬|u − v|ψ(u)ψ(v))/(∫ψ)²` over `[−1/2, 1/2]`; `H(ψ) = 2 − R(ψ)`. -/
def Rpsi (ψ : ℝ → ℝ) : ℝ :=
  ((∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u ^ 2)
    + ∫ u in (-(1 / 2 : ℝ))..(1 / 2), ∫ v in (-(1 / 2 : ℝ))..(1 / 2), |u - v| * ψ u * ψ v)
    / (∫ u in (-(1 / 2 : ℝ))..(1 / 2), ψ u) ^ 2

def Hpsi (ψ : ℝ → ℝ) : ℝ := 2 - Rpsi ψ

/-! ## κ, the charge of def:sigd-charge (moved here from node L7's file by the lead's ruling,
28 Sep 2026, so that A7 and A8 need not import L7) -/

/-- the charge `κ(λ) = [(λ − 2)₊² − c*]₊` of def:sigd-charge (l.1226). -/
def kappaCh (cstar t : ℝ) : ℝ := max ((max (t - 2) 0) ^ 2 - cstar) 0

end ZetaS

# ZetaShell: the family follow-up library

`ZetaShell` formalises the family paper (`papers/family/`): simple zeros on the critical line for the family of
primitive Dirichlet characters of conductor q ≤ Q, at height T = (log Q)^{r+ε}. It imports `ZetaQ` (the
conductor-aspect library of this repository, which imports `Zeta23`) and reuses its counting functions
`ZetaQ.NfamCount` (the family's zeros with T < γ ≤ 2T, counted with multiplicity) and `ZetaQ.N0sFamCount` (those that
are simple and on the critical line), its families (`ZetaQ.Family.qle`: conductors q ≤ Q) and its height
`ZetaQ.Twin`. Everything is in the namespace `ZetaShell`. Build it with `lake build ZetaShell` (it is not in
`defaultTargets`); the lakefile glob `ZetaShell.*` builds every module under `ZetaShell/`, whether or not the root
module `ZetaShell.lean` imports it.

## Groups

Modules are named `ZetaShell.<Group>.<File>`:

| group | contents |
|---|---|
| `Challenge`, `Interfaces` | the original Mathlib-only statement layer and the interfaces; their `sorry`s are the four original headline statements (with three displayed hypotheses each) and two tree-form headlines, kept unchanged |
| `Top/` | `HeadlineReduced`: the statements of record of the main theorem (hypothesis `ZeroDensityInput` only), with the proved implications to and from the original forms; `T1_Headline` |
| `Cert/` | the kernel-checked rational certificate: `certS53`, `certD53` |
| `PNT/` | the medium prime number theorem |
| `Density/`, `Frame/` | the proved nodes Z1–Z3 (from the zero-density input) and B1, F2 (count bridge, shell assembly) |
| `Defs/` | shared definitions; `Defs.Unify` proves repeated ones equal |
| `Farey/`, `Lemma2/` | the signed Farey identity, rectangles, hole-edge mass, Lemma 1′, Lemma 2 |
| `Design/` | the design layer at bandwidth 191/100 |
| `LemmaK/` | Lemma K and Theorem 1′ |
| `PropZ/` | the Proposition Z chain |
| `ShellS/`, `ShellK/` | the Theorem S side; Theorem K and the Frobenius row |
| `Skeleton/` | every module whose main declaration is an open statement (closed by `sorry`); see below |

## The two hypothesis-free theorems

**Theorem 1′ at 0.7235**, verbatim from `ZetaShell/LemmaK/LK_KT_Headline.lean`:

```lean
/-- **THEOREM 1′ at ZetaQ's own design profile, `P = 0.7235`.** -/
theorem theorem_one_prime_design (r ε : ℝ) (hr : 3 ≤ r) (hε : 0 < ε) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertKD : ℚ) : ℝ) - c * Real.log (Real.log (Qn : ℝ)) / Real.log (Qn : ℝ))
          * ZetaQ.NfamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε)
        ≤ ZetaQ.N0sFamCount ZetaQ.Family.qle Qn (ZetaQ.Twin (Qn : ℝ) r ε) (2 * ZetaQ.Twin (Qn : ℝ) r ε) := by
```

with, from `ZetaShell/Defs/LK_Defs.lean`,

```lean
/-- the constant of the design-profile route (no new design data): `0.7235`. -/
def PcertKD : ℚ := 7235 / 10000
```

Full name `ZetaShell.LemmaK.theorem_one_prime_design`. In words: for r ≥ 3 and ε > 0 there are Q₀ and c > 0 such that
for every Q ≥ Q₀, at least the proportion 0.7235 − c·log log Q / log Q of the zeros of the family q ≤ Q with
T < γ ≤ 2T, T = (log Q)^{r+ε}, are simple and on the critical line.

**The certificate of the main theorem**, verbatim from `ZetaShell/Cert/R4_CertS53.lean`:

```lean
theorem certS53 : CertS53 := by
```

with, from `ZetaShell/Challenge.lean`,

```lean
/-- **The certificate Prop (Track R)**: the profile is admissible at `λ`, meets L75, `1 < α′`, `1 < λ < 2`, and
`B_{α′}(v_p) ≤ 2 − P_c` at the kernel `(ℓ, α′, C⁺)`. -/
def ShellCert (S : ShellProfile) (Pc : ℚ) : Prop :=
  1 < (S.lam : ℝ) ∧ (S.lam : ℝ) < 2 ∧ 1 < (S.alphaP : ℝ) ∧ AdmissibleS S.lam S.v ∧ S.L75 ∧
    Bshell S.level S.alphaP S.Cplus S.v ≤ 2 - (Pc : ℝ)

/-- `0.9059137927` — the 10-digit truncation of `2 − B(v_{S53-L75})` (exact rational `0.90591379273786…`,
`p_cert_exact53.txt`). -/
def PcertS53 : ℚ := 9059137927 / 10000000000

/-- The certificate of the headline (sharp family). -/
def CertS53 : Prop := ShellCert S53L75 PcertS53
```

(the profile `S53L75` is defined in the same file). Full name `ZetaShell.certS53`: B(S53-L75) ≤ 2 − 0.9059137927.

Both depend only on `propext`, `Classical.choice` and `Quot.sound`, and on no `sorry`; check with

```bash
lake build ZetaShell
lake env lean comparator/PrintAxioms/FollowUpShell.lean
```

## The main theorem (hypothesis `ZeroDensityInput`)

**The Shell theorem at 0.9059137927**, the statement of record, verbatim from `ZetaShell/Top/HeadlineReduced.lean`:

```lean
theorem shell_S53_qle_reduced (hD : ZeroDensityInput) (r ε θ : ℝ) (hr : 3 ≤ r) (hε : 0 < ε)
    (hθ : 0 < θ) (hθ' : θ < 503 / 1994) :
    ∃ Q₀ c : ℝ, 0 < c ∧ ∀ Qn : ℕ, Q₀ ≤ (Qn : ℝ) →
      (((PcertS53 : ℚ) : ℝ) - c * Real.log (Qn : ℝ) ^ (-θ))
          * famN (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε)
        ≤ famN0s (modQle Qn) (twin (Qn : ℝ) r ε) (2 * twin (Qn : ℝ) r ε) := by
```

Full name `ZetaShell.shell_S53_qle_reduced`. `ZeroDensityInput` (`ZetaShell/Challenge.lean`, a structure with two
fields) is the pair of zero-density estimates (J) of Jutila and (M) of Montgomery, as quoted in the family paper; the
counts `famN`, `famN0s`, the family `modQle` and the height `twin` are defined in the same Mathlib-only file and are
those of `ZetaQ` (node B1, by `rfl`). The theorem depends only on `propext`, `Classical.choice` and `Quot.sound`, and
its proof reaches no `sorry` (census in `audit/followup/`). Its proof runs through the frame without the strong prime
number theorem (`Design.shell_frame_qle_of_K_noP`, `ShellK/LF_FrameNoP.lean`), Theorem K (`ShellK.thmK`), Theorem S
(`ShellS.shell_S`), Lemma 2(a) (`TrackF.lemma2a`), Proposition Z (`PropZ.propZ_W`) and the certificate `certS53`.
The same statement, over a file of definitions that imports Mathlib only, is the comparator statement
`family_simple_on_line_shell` (`comparator/Challenge/FollowUpFamily.lean`); check with

```bash
lake build ZetaShell Challenge.FollowUpFamily Solution.FollowUpFamily
lake env lean comparator/PrintAxioms/FollowUpFamily.lean
```

The original headline statements of `Challenge.lean` (with the hypotheses `PNTErrorTerm` and the certificate) follow
from the reduced ones by proved implications (`Top/HeadlineReduced.lean`). The dyadic and the bounded-height forms of
the statement of record are stated and open; they are not claimed, and the dyadic certificate `ZetaShell.certD53` is
a theorem whose constant is not claimed.

## `Skeleton/`

A module in `Skeleton/` carries an open node: its main declaration is stated and closed by `sorry`. When the node is
proved, the module moves to its group (and gets the group's module name); declaration names and statements stay the
same. Four modules were proved in place on 3 October 2026 and keep their `Skeleton/` names:
`Skeleton.L10_S1` (step S1 of Theorem S), `Skeleton.Astar_Corr` (the corrected primitive reduction A⋆),
`Skeleton.A2P_LineProfile` and `Skeleton.A2a_S3e_TailParts` (Lemma 2(a)); the other modules of `Skeleton/` carry open
statements, among them the first forms of nodes that were corrected (`L10_Z6d.Z6d_counts`, `L10_AS.AS_pointwise`),
which no proof uses. `lake build ZetaShell` therefore prints `declaration uses 'sorry'` warnings, for the `Skeleton/` modules and for
the statement files `Challenge`, `Interfaces` and `Top/HeadlineReduced`. A theorem outside these is not thereby free of
`sorry`, since it may use an open node: the census, which follows every proof term to the declarations that use
`sorry`, decides. The census of the release commit is in `audit/followup/`, and `RELEASE_NOTES.md` lists which theorems
rest on open statements.

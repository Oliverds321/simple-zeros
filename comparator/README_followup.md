# Comparator topic `FollowUpZeta`: the ζ follow-up paper

The files of this topic let a third party check, with [comparator](https://github.com/leanprover/comparator), **what** the
follow-up paper's Lean development proves about the zeros of Mathlib's `riemannZeta`. You do not need to read the proofs.

The general layout and the comparator conventions are in `README.md` in this directory.

## What is proved

Write N(T₁,T₂) for the nontrivial zeros ρ (0 < Re ρ < 1) with T₁ < Im ρ ≤ T₂, counted **with multiplicity**. The other
counts are:

| count | what it counts |
|---|---|
| Nˢ | simple zeros, on or off the critical line |
| N_d | distinct zeros |
| N₀ˢ | simple zeros on the critical line |
| N^sc | zeros on the critical line with multiplicity, plus simple zeros off the line |

"liminf X/N ≥ c" is written `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c − ε)·N(T) ≤ X(T)`. Twelve theorems follow from this table: each row,
on the dyadic windows (T, 2T] and on the cumulative windows (0, T] (`_cumulative`).

| theorem | liminf X/N ≥ | X | hypothesis |
|---|---|---|---|
| `zeta_simple_K5` | 0.675158622 | Nˢ | `CertAM5` |
| `zeta_distinct_K5` | 0.837579311 | N_d | `CertAM5` |
| `zeta_simple_K7` | 0.676102666 | Nˢ | `CertAM7` |
| `zeta_distinct_K7` | 0.838051333 | N_d | `CertAM7` |
| `zeta_simple_on_line` | 0.6733736895 | N₀ˢ | `CertS8` |
| `zeta_simple_or_critical` | 0.8879195 | N^sc | `CertS8` |

**Non-vacuity companions.** Two further theorems have no hypothesis:
- `zeta_zerosIn_finite`: every window is finite, so the counts are genuine and not Lean's 0 for an infinite set;
- `zeta_tendsto_Ncount`: N(T, 2T) → ∞.

**Axioms.** All fourteen theorems use only `propext`, `Classical.choice` and `Quot.sound`. None contains `sorry` or
`native_decide`, and none declares an `axiom`. The certificate Props enter as explicit hypotheses, not as axioms.

## Trusted and untrusted files

| file | trusted? | role |
|---|---|---|
| `ChallengeDeps.lean` | yes | zeros, `zeroMult` (Mathlib's `analyticOrderAt`), windows, `Ncount`, `Nsimple`, `Ndist`, `N0simple` |
| `ChallengeDeps/FollowUpZeta.lean` | yes | `Nsc`; the windows ψ = cos 1.6s and ψ̃; the kernel k_ψ; the local inequalities; the three certificate Props |
| `Challenge/FollowUpZeta.lean` | yes | the fourteen statements, proofs `sorry` |
| `config-followup.json` | yes | the theorem names and the permitted axioms |
| `Solution/FollowUpZeta.lean`, libraries `ZetaS`, `Zeta23` | no | the proofs; comparator checks them |

## How to check

The quick check needs no extra tooling. Every line must read `… depends on axioms: [propext, Classical.choice, Quot.sound]`.

```bash
lake build Solution.FollowUpZeta
lake env lean comparator/PrintAxioms/FollowUpZeta.lean
```

**Full comparator run.** Follow the steps of `README.md`, with the config of this topic:

```bash
lake env /path/to/comparator comparator/config-followup.json
```

Comparator:
- builds `Challenge.FollowUpZeta` and `Solution.FollowUpZeta` in its sandbox;
- checks that the fourteen statements coincide;
- audits the axioms;
- replays the proofs in the kernel (optionally also in nanoda).

## The certificate hypotheses

**What each Prop asserts.** Some weights with the stated constants satisfy an explicit inequality between finitely many
real numbers built from the kernel k_ψ. The inequality must hold at every point of the orthant [0,∞)^{K−1}. For the all-marks
Props it must also hold for every mark pattern in {1,2}^K.

**Where the witnesses are.** In exact-rational data files, identified by sha256 in the doc-strings of
`ChallengeDeps/FollowUpZeta.lean`. These files, and the certifier scripts, are part of the paper's supplementary material.
In this repository they are in `supplementary/certificates/` (map: `supplementary/README.md`).

**How the inequality was established.** By interval branch-and-bound in Arb ball arithmetic. The certifiers are:
- python-flint for `bnb_lb3.py` and `bnb_lb3_w.py`;
- mpmath for `bnb_interval_w.py`.

**How the certifiers cover the orthant:**
- a box is accepted only when a rigorous lower bound is strictly above the claim;
- the unbounded part of the orthant is discarded exactly, because the functional is at least (min μ)·Σg there;
- mark patterns are grouped into reversal classes, which is valid because the weights are exactly reversal-symmetric.

The reduction from classes to all patterns is a Lean theorem of the development.

| Prop | data | how to reproduce |
|---|---|---|
| `CertS8` (K = 8, ν = 7/1700, c = 0.00796) | `w_poly8A_K8_mu1700.json`, `win_poly8A.json` | `python -u bnb_lb3.py poly8A 8 1700 0.00796 --weights w_poly8A_K8_mu1700.json --window win_poly8A.json --lb3 --sym --qp-sweeps 6` (sharded driver: `mkinit.sh`, `round_lb3.sh`; about 4.5·10⁸ boxes). Must end `ALL SHARDS OK`. |
| `CertAM7` (K = 7) | `claims_a1.6_K7_mu500_L1e5.json` and 72 `xpat_K7_*.json` | `runlb3.sh 1.6 7 500 <claims> <dir> <log> <timeout> <72 patterns>`, i.e. `bnb_lb3_w.py 1.6 7 500 <claim> --weights xpat_K7_<p>.json --lb3 [--sym]`. Every line must read `ok: True`. |
| `CertAM5` (K = 5) | `claims_a1.6_K5_mu500.json` and 20 `xpat_K5_*.json` | `runcert.sh 1.6 5 500 <claims> <log> <20 patterns>` (`bnb_interval_w.py`). 20/20 `ok: True`. |

**Exact-rational side conditions** can be checked without any interval arithmetic. They are:
- Σ_i γ_{s,i} = 2 for every span s;
- ν, a₁ and a₂ are the stated values;
- the pattern weights are γ·m_i·m_{i+s};
- each claim is Σ_i b_i(m_i);
- the weights are reversal-symmetric;
- the classes cover all patterns.

The checkers are `verify_inputs.py` and the audit script `d819_exact.py`, in `supplementary/certificates/common/`; the
commands are in `supplementary/VERIFY.md`.

**Status.**
- The majorant certificate of the paper's Lemma "separated sites have room" is **not** a hypothesis. It is a theorem of the
  development: 614 cells replayed by the Lean kernel.
- The kernel replay of the K = 5 certificate was completed on 28 September 2026: the library `ZetaSReplay`
  (`lake build ZetaSReplay`; `ZetaSReplay/README.md`) proves `CertAM5`, and its module `ReplayHeadlines` states the two
  K = 5 theorems without the hypothesis. In the fourteen statements of this topic, `CertAM5` remains a displayed
  hypothesis like `CertAM7` and `CertS8`.

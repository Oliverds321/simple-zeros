/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- `#print axioms` for the K = 5 kernel replay (library ZetaSReplay; run `lake build ZetaSReplay` first, about
   20 Lean-hours). The first two are the K = 5 theorems without the hypothesis `CertAM5`; the third is `CertAM5` itself.
   Every line must read '<name>' depends on axioms: [propext, Classical.choice, Quot.sound] -/
import ReplayHeadlines

#print axioms ZetaS.Top.zeta_simple_K5_uncond
#print axioms ZetaS.Top.zeta_distinct_K5_uncond
#print axioms ZetaS.CertV2.certAM5_replayed

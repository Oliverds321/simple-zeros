/-
Copyright (c) 2026 Oliver D'Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/- `#print axioms` for the two hypothesis-free theorems of the family library ZetaShell (run `lake build ZetaShell`
   first): Theorem 1′ at 0.7235 and the certificate B(S53-L75) ≤ 2 − 0.9059137927. Every line must read
   '<name>' depends on axioms: [propext, Classical.choice, Quot.sound] -/
import ZetaShell.LemmaK.LK_KT_Headline
import ZetaShell.Cert.R4_CertS53

#print axioms ZetaShell.LemmaK.theorem_one_prime_design
#print axioms ZetaShell.certS53

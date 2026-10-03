# papers

The two papers of the follow-up, each with its LaTeX sources and its PDF.

| folder | paper (working title) | Lean side | data |
|---|---|---|---|
| `zeta/` | "On the proportions of simple and of distinct zeros of the Riemann zeta function" | library `ZetaS`, the replay `ZetaSReplay`, the comparator topic `FollowUpZeta` (`comparator/README_followup.md`) | `supplementary/` |
| `family/` | "Simple zeros on the critical line of primitive Dirichlet L-functions on average over moduli q ≤ Q: the killed kernel and the Shell kernel" | library `ZetaShell` (`ZetaShell/README.md`), the comparator topic `FollowUpFamily` (`comparator/README_followup_family.md`) | the certificates are Lean theorems (`ZetaShell/Cert/`) |

The results of both papers, with their Lean names and trust levels, are tabulated in the top-level `README.md`
(section "Follow-up (Oliver D'Souza, October 2026)"); what is not claimed is listed in `RELEASE_NOTES.md`. Where a
paper and the Lean library differ, the Lean statement is the one that is checked. Licence of the papers' text: CC BY 4.0
(see `NOTICE`); the Lean code is under the Apache License, Version 2.0.

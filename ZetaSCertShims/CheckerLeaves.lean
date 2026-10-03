/-
Bare-name forwarding module (integrator L0_5, 28 Sep 2026). The checker v3 files in ZetaS/Cert/ are FROZEN
(byte-identical to L1_1c's audited files, sha256 recorded in rh72/lean_board/reports/L0_5_integration.md) and import
each other by bare module names. This module only re-exports the library module `ZetaS.Cert.CheckerLeaves`, so that there is
exactly one copy of every declaration. New code: `import ZetaS.Cert.CheckerLeaves`.
-/
import ZetaS.Cert.CheckerLeaves

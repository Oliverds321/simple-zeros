/-
lean_work/L1_1/CheckerCoreV3.lean — the track C checker, version 3 (L1_1c, 28 Sep 2026): umbrella module.
= `CheckerBase` (byte-identical to CheckerCore lines 18–163) + `CheckerLeaves` (lpSpan fixed; additions).
Replaces `CheckerCore` everywhere (same namespace `ZetaS.CertV2`, same declaration names; the two cannot be imported
together). Core Lean only.
-/
import CheckerBase
import CheckerLeaves

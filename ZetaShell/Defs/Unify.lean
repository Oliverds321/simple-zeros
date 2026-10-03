/-
ZetaShell/Defs/Unify.lean (L0_6, integration of the family library, 28 Sep 2026).

Definitions that the work folders repeat under different namespaces. Both copies are KEPT as definitions (the proofs
that unfold them are untouched); this module proves that each pair is equal, by `rfl`, so that a consumer can pass
from one name to the other. Pairs:
- Track F (`ZetaShell.TrackF`, `Defs/TF_Defs.lean`, L7_6; also used by L7_8) and
  Lemma K (`ZetaShell.LemmaK`, `Defs/LK_Defs.lean`, L7_3; also used by L7_7 and L7_9):
  `distZ`, `Ddens`, `DTk`/`DT`, `acoefS`/`acoef`;
Not unified by a theorem here: the exact-rational certificate code `ZetaShell.CertQ` (`Cert/ShellCertQ.lean`,
L7_1) and its copy `ZetaShell.LemmaK.CertQ` (`LemmaK/LK_KCq.lean`, L7_3), whose recursive list functions are separate
definitions (equal only by induction, not by `rfl`); and (different objects, listed "to unify" in the integration report): `ShellProfile` (L7_1) and
`KProfile` (L7_3); L7_7's `shellFrame_toKFrame` is the bridge between the frames built on them.
-/
import ZetaShell.Defs.TF_Defs
import ZetaShell.Defs.LK_Defs

namespace ZetaShell
namespace Defs

theorem distZ_trackF_eq_lemmaK : TrackF.distZ = LemmaK.distZ := rfl

theorem Ddens_trackF_eq_lemmaK {ι : Type} : @TrackF.Ddens ι = @LemmaK.Ddens ι := rfl

theorem DTk_trackF_eq_DT_lemmaK : TrackF.DTk = LemmaK.DT := rfl

theorem acoefS_trackF_eq_acoef_lemmaK : TrackF.acoefS = LemmaK.acoef := rfl

end Defs
end ZetaShell

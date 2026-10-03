/-
lean_work/L5_2/CertMajV2Proof.lean — L5_2, 28 Sep 2026. **`CertMajV2` from the kernel-replayed cell certificates.**

  NPos  : 600 cells on [0, 30] (shards NPosS0..NPosS11), third-order cell bound, checker `MajCheck.cellOk`;
  NMaj2 : 14 cells on [0, 1/2] (shard NMajS0), second-order cell bound (|g″| ≤ 7), checker `MajCheck.majOk`.

  `certMajV2_of_CNodes : CNodes → CertMajV2`   — no numerical hypothesis; the only hypothesis is the bundle of the
                                                 track-C node statements C05 (sinQI/cosQI) and C06 (sinCosPiQ, sinA);
  `certMajV2_proved    : CertMajV2`           — the same, instantiated with the node statements (`sorryAx` = C05/C06
                                                 until L5_1's proofs are swapped in).
-/
import ZetaS.Majorant.NPosProof
import ZetaS.Majorant.MajSoundNMaj
import ZetaS.Majorant.Shards.NMajS0
import ZetaS.Majorant.CertMajV2

open Real

noncomputable section

namespace ZetaS.MajSound

open ZetaS.MCert ZetaS.MajCheck

/-- **NMaj2 from the certificate**, given the C-node statements. -/
theorem nmaj2_of_CNodes (hC : CNodes) : NMaj2 := by
  refine nmaj2_of_gM fun s hs => ?_
  have hl : lastD 2097152 [4194304, 5242880, 6291456, 6815744, 7340032, 7602176, 7864320, 7995392, 8126464, 8192000, 8257536, 8323072, 8388608] = 8388608 := rfl
  refine majChainOk_sound hC _ _ _ NMajS0_ok s ?_ ?_
  · norm_num; exact hs.1
  · rw [hl]; norm_num; exact hs.2

/-- **CertMajV2**, with no numerical hypothesis: only the track-C node statements C05/C06 (`CNodes`). -/
theorem certMajV2_of_CNodes (hC : CNodes) : CertMajV2 :=
  certMajV2_of_NPos_NMaj2 (npos_of_CNodes hC) (nmaj2_of_CNodes hC)

/-- **CertMajV2**, instantiated with the C05/C06 node statements. -/
theorem certMajV2_proved : CertMajV2 := certMajV2_of_CNodes cnodes_of_statements

end ZetaS.MajSound

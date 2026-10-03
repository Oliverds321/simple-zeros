/- replay: the K = 5 all-marks certificate, all 20 classes (L1_1d). Applies `ZetaS.CertV2.ChainV3.certAM5_of_checks` (library module ZetaS.Cert.ChainV3), the level-A
   soundness chain of L5_2 (v3chain/ChainV3.lean); hdata holds by `rfl` (each cert has data `classData m`). -/
import ZetaS.Cert.ChainV3
import R11111_Cert
import R11112_Cert
import R11121_Cert
import R11122_Cert
import R11211_Cert
import R11212_Cert
import R11221_Cert
import R11222_Cert
import R12112_Cert
import R12121_Cert
import R12122_Cert
import R12212_Cert
import R12221_Cert
import R12222_Cert
import R21112_Cert
import R21122_Cert
import R21212_Cert
import R21222_Cert
import R22122_Cert
import R22222_Cert

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2

theorem certAM5_replayed : ZetaS.CertAM5 :=
  ChainV3.certAM5_of_checks [R11111.cert, R11112.cert, R11121.cert, R11122.cert, R11211.cert, R11212.cert, R11221.cert, R11222.cert, R12112.cert, R12121.cert, R12122.cert, R12212.cert, R12221.cert, R12222.cert, R21112.cert, R21122.cert, R21212.cert, R21222.cert, R22122.cert, R22222.cert] rfl
    (List.forall_mem_cons.mpr ⟨R11111.cert_ok, List.forall_mem_cons.mpr ⟨R11112.cert_ok, List.forall_mem_cons.mpr ⟨R11121.cert_ok, List.forall_mem_cons.mpr ⟨R11122.cert_ok, List.forall_mem_cons.mpr ⟨R11211.cert_ok, List.forall_mem_cons.mpr ⟨R11212.cert_ok, List.forall_mem_cons.mpr ⟨R11221.cert_ok, List.forall_mem_cons.mpr ⟨R11222.cert_ok, List.forall_mem_cons.mpr ⟨R12112.cert_ok, List.forall_mem_cons.mpr ⟨R12121.cert_ok, List.forall_mem_cons.mpr ⟨R12122.cert_ok, List.forall_mem_cons.mpr ⟨R12212.cert_ok, List.forall_mem_cons.mpr ⟨R12221.cert_ok, List.forall_mem_cons.mpr ⟨R12222.cert_ok, List.forall_mem_cons.mpr ⟨R21112.cert_ok, List.forall_mem_cons.mpr ⟨R21122.cert_ok, List.forall_mem_cons.mpr ⟨R21212.cert_ok, List.forall_mem_cons.mpr ⟨R21222.cert_ok, List.forall_mem_cons.mpr ⟨R22122.cert_ok, List.forall_mem_cons.mpr ⟨R22222.cert_ok, fun _ h => by simp at h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)

end ZetaS.CertV2

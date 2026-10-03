import R12122_Data
import R12122_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R12122

def L4561 : Leaf := Leaf.cap
theorem L4561_ok : Leaf.check D_R12122 [((75/16),(75/8)),((373/128),(373/64)),((0),(373/64)),((0),(75/16))] L4561 = true := by decide +kernel

def L4562 : Leaf := Leaf.cap
theorem L4562_ok : Leaf.check D_R12122 [((75/16),(75/8)),((0),(373/64)),((0),(373/64)),((75/16),(75/8))] L4562 = true := by decide +kernel

end R12122
end ZetaS.CertV2

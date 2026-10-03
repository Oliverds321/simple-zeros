import R11212_Data
import R11212_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R11212

def L5520 : Leaf := Leaf.cap
theorem L5520_ok : Leaf.check D_R11212 [((587/128),(587/64)),((0),(365/64)),((0),(365/64)),((587/128),(587/64))] L5520 = true := by decide +kernel

end R11212
end ZetaS.CertV2

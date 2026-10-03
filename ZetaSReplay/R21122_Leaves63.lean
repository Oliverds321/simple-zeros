import R21122_Data
import R21122_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R21122

def L5043 : Leaf := Leaf.cap
theorem L5043_ok : Leaf.check D_R21122 [((1803/256),(601/64)),((0),(187/64)),((0),(187/64)),((601/256),(601/128))] L5043 = true := by decide +kernel

def L5044 : Leaf := Leaf.cap
theorem L5044_ok : Leaf.check D_R21122 [((601/128),(601/64)),((0),(187/64)),((187/64),(187/32)),((0),(601/128))] L5044 = true := by decide +kernel

def L5045 : Leaf := Leaf.cap
theorem L5045_ok : Leaf.check D_R21122 [((601/128),(601/64)),((187/64),(187/32)),((0),(187/32)),((0),(601/128))] L5045 = true := by decide +kernel

def L5046 : Leaf := Leaf.cap
theorem L5046_ok : Leaf.check D_R21122 [((601/128),(601/64)),((0),(187/32)),((0),(187/32)),((601/128),(601/64))] L5046 = true := by decide +kernel

end R21122
end ZetaS.CertV2

import R12222_Data
import R12222_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R12222

def L4003 : Leaf := Leaf.cap
theorem L4003_ok : Leaf.check D_R12222 [((1887/256),(629/64)),((0),(391/128)),((0),(391/128)),((629/256),(629/128))] L4003 = true := by decide +kernel

def L4004 : Leaf := Leaf.cap
theorem L4004_ok : Leaf.check D_R12222 [((629/128),(629/64)),((0),(391/128)),((391/128),(391/64)),((0),(629/128))] L4004 = true := by decide +kernel

def L4005 : Leaf := Leaf.cap
theorem L4005_ok : Leaf.check D_R12222 [((629/128),(629/64)),((391/128),(391/64)),((0),(391/64)),((0),(629/128))] L4005 = true := by decide +kernel

def L4006 : Leaf := Leaf.cap
theorem L4006_ok : Leaf.check D_R12222 [((629/128),(629/64)),((0),(391/64)),((0),(391/64)),((629/128),(629/64))] L4006 = true := by decide +kernel

end R12222
end ZetaS.CertV2

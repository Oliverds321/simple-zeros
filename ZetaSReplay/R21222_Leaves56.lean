import R21222_Data
import R21222_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R21222

def L4489 : Leaf := Leaf.cap
theorem L4489_ok : Leaf.check D_R21222 [((4725/512),(315/32)),((0),(49/64)),((0),(49/64)),((315/512),(315/256))] L4489 = true := by decide +kernel

def L4490 : Leaf := Leaf.cap
theorem L4490_ok : Leaf.check D_R21222 [((2205/256),(315/32)),((0),(49/64)),((49/64),(49/32)),((0),(315/256))] L4490 = true := by decide +kernel

def L4491 : Leaf := Leaf.cap
theorem L4491_ok : Leaf.check D_R21222 [((2205/256),(315/32)),((49/64),(49/32)),((0),(49/32)),((0),(315/256))] L4491 = true := by decide +kernel

def L4492 : Leaf := Leaf.cap
theorem L4492_ok : Leaf.check D_R21222 [((2205/256),(315/32)),((0),(49/32)),((0),(49/32)),((315/256),(315/128))] L4492 = true := by decide +kernel

def L4493 : Leaf := Leaf.cap
theorem L4493_ok : Leaf.check D_R21222 [((945/128),(315/32)),((0),(49/32)),((49/32),(49/16)),((0),(315/128))] L4493 = true := by decide +kernel

def L4494 : Leaf := Leaf.cap
theorem L4494_ok : Leaf.check D_R21222 [((945/128),(315/32)),((49/32),(49/16)),((0),(49/16)),((0),(315/128))] L4494 = true := by decide +kernel

def L4495 : Leaf := Leaf.cap
theorem L4495_ok : Leaf.check D_R21222 [((945/128),(315/32)),((0),(49/16)),((0),(49/16)),((315/128),(315/64))] L4495 = true := by decide +kernel

def L4496 : Leaf := Leaf.cap
theorem L4496_ok : Leaf.check D_R21222 [((315/64),(315/32)),((0),(49/16)),((49/16),(49/8)),((0),(315/64))] L4496 = true := by decide +kernel

def L4497 : Leaf := Leaf.cap
theorem L4497_ok : Leaf.check D_R21222 [((315/64),(315/32)),((49/16),(49/8)),((0),(49/8)),((0),(315/64))] L4497 = true := by decide +kernel

def L4498 : Leaf := Leaf.cap
theorem L4498_ok : Leaf.check D_R21222 [((315/64),(315/32)),((0),(49/8)),((0),(49/8)),((315/64),(315/32))] L4498 = true := by decide +kernel

end R21222
end ZetaS.CertV2

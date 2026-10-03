import R11211_Data
import R11211_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R11211

def L4327 : Leaf := Leaf.cap
theorem L4327_ok : Leaf.check D_R11211 [((987/128),(141/16)),((351/512),(351/256)),((0),(351/256)),((0),(141/128))] L4327 = true := by decide +kernel

def L4328 : Leaf := Leaf.cap
theorem L4328_ok : Leaf.check D_R11211 [((987/128),(141/16)),((0),(351/256)),((0),(351/256)),((141/128),(141/64))] L4328 = true := by decide +kernel

def L4329 : Leaf := Leaf.cap
theorem L4329_ok : Leaf.check D_R11211 [((423/64),(141/16)),((0),(351/256)),((351/256),(351/128)),((0),(141/64))] L4329 = true := by decide +kernel

def L4330 : Leaf := Leaf.cap
theorem L4330_ok : Leaf.check D_R11211 [((423/64),(141/16)),((351/256),(351/128)),((0),(351/128)),((0),(141/64))] L4330 = true := by decide +kernel

def L4331 : Leaf := Leaf.cap
theorem L4331_ok : Leaf.check D_R11211 [((423/64),(141/16)),((0),(351/128)),((0),(351/128)),((141/64),(141/32))] L4331 = true := by decide +kernel

def L4332 : Leaf := Leaf.cap
theorem L4332_ok : Leaf.check D_R11211 [((141/32),(141/16)),((0),(351/128)),((351/128),(351/64)),((0),(141/32))] L4332 = true := by decide +kernel

def L4333 : Leaf := Leaf.cap
theorem L4333_ok : Leaf.check D_R11211 [((141/32),(141/16)),((351/128),(351/64)),((0),(351/64)),((0),(141/32))] L4333 = true := by decide +kernel

def L4334 : Leaf := Leaf.cap
theorem L4334_ok : Leaf.check D_R11211 [((141/32),(141/16)),((0),(351/64)),((0),(351/64)),((141/32),(141/16))] L4334 = true := by decide +kernel

end R11211
end ZetaS.CertV2

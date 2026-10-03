import R11111_Data
import R11111_Cells

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ZetaS.CertV2
namespace R11111

def L3444 : Leaf := Leaf.cap
theorem L3444_ok : Leaf.check D_R11111 [((1605/256),(535/64)),((333/256),(333/128)),((0),(333/128)),((0),(535/256))] L3444 = true := by decide +kernel

def L3445 : Leaf := Leaf.cap
theorem L3445_ok : Leaf.check D_R11111 [((1605/256),(535/64)),((0),(333/128)),((0),(333/128)),((535/256),(535/128))] L3445 = true := by decide +kernel

def L3446 : Leaf := Leaf.cap
theorem L3446_ok : Leaf.check D_R11111 [((535/128),(535/64)),((0),(333/128)),((333/128),(333/64)),((0),(535/128))] L3446 = true := by decide +kernel

def L3447 : Leaf := Leaf.cap
theorem L3447_ok : Leaf.check D_R11111 [((535/128),(535/64)),((333/128),(333/64)),((0),(333/64)),((0),(535/128))] L3447 = true := by decide +kernel

def L3448 : Leaf := Leaf.cap
theorem L3448_ok : Leaf.check D_R11111 [((535/128),(535/64)),((0),(333/64)),((0),(333/64)),((535/128),(535/64))] L3448 = true := by decide +kernel

end R11111
end ZetaS.CertV2

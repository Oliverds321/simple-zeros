/-
lean_work/L5_2/MajCheck.lean — L5_2, 28 Sep 2026. Cell checker for the majorant node NPos (core Lean only; imports
L1_1's checker base `CheckerBase` (v3; byte-identical to the base part of v2) for `QI` and the enclosure `sinCosPiQ`, whose soundness is node C06).

Per cell [a, b], a = A/2^24, b = B/2^24, m = (a+b)/2, r = (b−a)/2, θ = πm/30:
  * one enclosure (sin θ, cos θ) = sinCosPiQ (m/30); fixed-point start z₁ = (C₁, S₁) ∈ ℤ² (scale 2⁻⁶⁴), error ≤ 2⁻⁵⁶;
  * z_{j+1} = ⌊z_j · z₁ / 2⁶⁴⌋ (complex product, floor division) — the rotation recurrence; its error grows only
    LINEARLY in j (Euclidean norm; proved in MajSound.lean), unlike an interval recurrence;
  * exact integer sums a₀ = Σ B_j C_j, a₁ = Σ j B_j S_j, a₂ = Σ j² B_j C_j (B_j = 2⁶⁰ β_j exactly), scale 2⁻¹²⁴;
  * the third-order cell bound P(m) − |P′(m)| r + min(0, P″(m)) r²/2 − (645/6) r³ ≥ 0 with rigorous error terms.
Python mirror: py/majcert.py (`npos_lb`).
-/
import ZetaS.Cert.CheckerBase

namespace ZetaS.MajCheck
open ZetaS.CertV2

/-- 2⁶⁴. -/
def TK : Int := 18446744073709551616

/-- one step of the fixed-point rotation recurrence `z ↦ ⌊z · (C₁ + i S₁) / 2⁶⁴⌋`. -/
def rot (C1 S1 : Int) (z : Int × Int) : Int × Int :=
  ((z.1 * C1 - z.2 * S1) / TK, (z.1 * S1 + z.2 * C1) / TK)

/-- (B_j, j B_j, j² B_j), j = 1..59, B_j = 2⁶⁰ β_j (exact). -/
def trip : List (Int × Int × Int) :=
  [(1784063540185802752, 1784063540185802752, 1784063540185802752),
   (1771801927013617920, 3543603854027235840, 7087207708054471680),
   (1754793691309126144, 5264381073927378432, 15793143221782135296),
   (1733500362815620096, 6934001451262480384, 27736005805049921536),
   (1708247229072857344, 8541236145364286720, 42706180726821433600),
   (1678915210047483392, 10073491260284900352, 60440947561709402112),
   (1645950624269847552, 11521654369888932864, 80651580589222530048),
   (1609688969841816064, 12877511758734528512, 103020094069876228096),
   (1570242419847852032, 14132181778630668288, 127189636007676014592),
   (1527913336650664192, 15279133366506641920, 152791333665066419200),
   (1482965995345412864, 16312625948799541504, 179438885436794956544),
   (1435610346019879424, 17227324152238553088, 206727889826862637056),
   (1386187448038348544, 18020436824498531072, 234265678718480903936),
   (1334965326676127232, 18689514573465781248, 261653204028520937472),
   (1282178245674879488, 19232673685123192320, 288490105276847884800),
   (1228028511439941120, 19648456183039057920, 314375298928624926720),
   (1172893530433400320, 19939190017367805440, 338966230295252692480),
   (1116954536102012928, 20105181649836232704, 361893269697052188672),
   (1060498663065169408, 20149474598238218752, 382840017366526156288),
   (1003780077406281216, 20075601548125624320, 401512030962512486400),
   (947002408640309120, 19887050581446491520, 417628062210376321920),
   (890357322623154560, 19587861097709400320, 430932944149606807040),
   (834244078790684800, 19187613812185750400, 441315117680272259200),
   (778661140567859584, 18687867373628630016, 448508816967087120384),
   (724002236791723136, 18100055919793078400, 452501397994826960000),
   (670304870031020928, 17427926620806544128, 453126092140970147328),
   (617853335103623296, 16682040047797828992, 450415081290541382784),
   (566783173001420608, 15869928844039777024, 444358007633113756672),
   (517283723277302272, 15001227975041765888, 435035611276211210752),
   (469498782406220608, 14084963472186618240, 422548904165598547200),
   (423485273735010560, 13128043485785327360, 406969348059345148160),
   (379480881660652608, 12143388213140883456, 388588422820508270592),
   (337523307485738624, 11138269147029374592, 367562881851969361536),
   (297714986021474880, 10122309524730145920, 344158523840824961280),
   (260213104109884256, 9107458643845948960, 318761052534608213600),
   (224904578893787392, 8096564840176346112, 291476334246348460032),
   (192038272162547360, 7105416070014252320, 262900394590527335840),
   (161503594608983776, 6137136595141383488, 233211190615372572544),
   (133456120113503456, 5204788684426634784, 202986758692638756576),
   (107772541395670160, 4310901655826806400, 172436066233072256000),
   (84528497262521088, 3465668387763364608, 142092403898297948928),
   (63652114136224288, 2673388793721420096, 112282329336299644032),
   (45145197556697696, 1941243494938000928, 83473470282334039904),
   (28975793541368760, 1274934915820225440, 56097136296089919360),
   (15052867123099924, 677379020539496580, 30482055924277346100),
   (3244331135236463, 149239232220877298, 6865004682160355708),
   (-6424779319822946, -301964628031678462, -14192337517488887714),
   (-14137190789931978, -678585157916734944, -32572087580003277312),
   (-19941857667944748, -977151025729292652, -47880400260735339948),
   (-23963677543891032, -1198183877194551600, -59909193859727580000),
   (-26434949697422464, -1348182434568545664, -68757304162995828864),
   (-27398914329024984, -1424743545109299168, -74086664345683556736),
   (-26976022559692548, -1429729195663705044, -75775647370176367332),
   (-25373830557264896, -1370186850092304384, -73990089904984436736),
   (-22720902056862312, -1249649613127427160, -68730728722008493800),
   (-19251487307749796, -1078083289233988576, -60372664197103360256),
   (-15173675432115916, -864899499630607212, -49299271478944611084),
   (-10395421134649716, -602934425809683528, -34970196696961644624),
   (-5309413051505067, -313255370038798953, -18482066832289138227)]

/-- β₀. -/
def b0 : Rat := 1751508895300479 / 1125899906842624

/-- the accumulation over `trip`, starting from z = z₁. -/
def acc (C1 S1 : Int) : List (Int × Int × Int) → Int × Int → Int × Int × Int → Int × Int × Int
  | [], _, a => a
  | b :: bs, z, a => acc C1 S1 bs (rot C1 S1 z) (a.1 + b.1 * z.1, a.2.1 + b.2.1 * z.2, a.2.2 + b.2.2 * z.1)

def eps0 : Rat := 1 / 72057594037927936          -- 2⁻⁵⁶
def dlt : Rat := 1 / 562949953421312              -- 2⁻⁴⁹
def piHi : Rat := 31416 / 10000
def sc124 : Rat := 1 / 21267647932558653966460912964485513216   -- 2⁻¹²⁴
def sc64 : Rat := 18446744073709551616

/-- fixed-point start and its error, from the enclosure `sinCosPiQ x = (sin πx, cos πx)`. -/
def startErr (sc : QI × QI) (C1 S1 : Int) : Rat :=
  max (sc.2.hi - (C1 : Rat) / sc64) ((C1 : Rat) / sc64 - sc.2.lo) +
    max (sc.1.hi - (S1 : Rat) / sc64) ((S1 : Rat) / sc64 - sc.1.lo)

/-- the final inequality of a cell, from the three sums and the radius. -/
def lbOk (a : Int × Int × Int) (r : Rat) : Bool :=
  decide (0 ≤ b0 + 2 * ((a.1 : Rat) * sc124) - 236 * dlt
    - piHi / 15 * (qabs ((a.2.1 : Rat) * sc124) + 6962 * dlt) * r
    - piHi * piHi / 900 * max 0 ((a.2.2 : Rat) * sc124 + 410758 * dlt) * r * r - 645 / 6 * r * r * r)

def cellCore (sc : QI × QI) (C1 S1 : Int) (r : Rat) : Bool :=
  decide (startErr sc C1 S1 ≤ eps0) && lbOk (acc C1 S1 trip (C1, S1) (0, 0, 0)) r

/-- the NPos check of the cell [A/2²⁴, B/2²⁴]. -/
def cellOk (A B : Nat) : Bool :=
  let m : Rat := ((A + B : Nat) : Rat) / 33554432
  let r : Rat := ((B - A : Nat) : Rat) / 33554432
  let sc := sinCosPiQ (m / 30)
  cellCore sc (sc.2.lo * sc64).floor (sc.1.lo * sc64).floor r

/-- a chain of consecutive cells given by its breakpoints. -/
def chainOk : List Nat → Bool
  | a :: b :: rest => cellOk a b && chainOk (b :: rest)
  | _ => true

theorem chainOk_cons {a b : Nat} {rest : List Nat} (h : cellOk a b = true) (h' : chainOk (b :: rest) = true) :
    chainOk (a :: b :: rest) = true := by
  show (cellOk a b && chainOk (b :: rest)) = true
  rw [h, h']; rfl

theorem chainOk_single (a : Nat) : chainOk [a] = true := rfl

/-! ## NMaj2: g(s) = (1/60) σ(πs/60)² P(s) − cos(8s/5)/Z, Z = (5/4) sin(4/5), σ(x) = 1 − x²/6 − x⁴/100.
Second-order cell bound g(s) ≥ g(m) − |g′(m)| r − (7/2) r² (|g″| ≤ 7 on [−1, 1], MajSound.lean). -/

/-- enclosures of (g(m), g′(m)) from the three sums at m (only a₀, a₁ are used). -/
def gEncl (m : Rat) (a : Int × Int × Int) : QI × QI :=
  let SP : Rat := b0 + 2 * ((a.1 : Rat) * sc124)
  let PI : QI := ⟨SP - 236 * dlt, SP + 236 * dlt⟩
  let SD : Rat := (a.2.1 : Rat) * sc124
  let P1I : QI := QI.mul (QI.smul (-1 / 15) piQ) ⟨SD - 6962 * dlt, SD + 6962 * dlt⟩
  let X : QI := QI.smul (m / 60) piQ
  let X2 : QI := QI.sq X
  let sig : QI := QI.sub (QI.sub (QI.pt 1) (QI.smul (1 / 6) X2)) (QI.smul (1 / 100) (QI.sq X2))
  let sigp : QI := QI.sub (QI.smul (-1 / 3) X) (QI.smul (1 / 25) (QI.mul X2 X))
  let q : QI := QI.sq sig
  let q1 : QI := QI.smul 2 (QI.mul (QI.mul sig sigp) (QI.smul (1 / 60) piQ))
  let Zi : QI := QI.inv (QI.smul (5 / 4) sinA)
  let cI : QI := cosQI 9 (QI.pt (8 * m / 5))
  let sI : QI := sinQI 9 (QI.pt (8 * m / 5))
  (QI.sub (QI.smul (1 / 60) (QI.mul q PI)) (QI.mul cI Zi),
   QI.add (QI.smul (1 / 60) (QI.add (QI.mul q1 PI) (QI.mul q P1I))) (QI.smul (8 / 5) (QI.mul sI Zi)))

def gLbOk (g : QI × QI) (r : Rat) : Bool := decide (0 ≤ g.1.lo - g.2.absMax * r - 7 / 2 * r * r)

def majCore (sc : QI × QI) (C1 S1 : Int) (m r : Rat) : Bool :=
  decide (startErr sc C1 S1 ≤ eps0) && gLbOk (gEncl m (acc C1 S1 trip (C1, S1) (0, 0, 0))) r

/-- the NMaj2 check of the cell [A/2²⁴, B/2²⁴] ⊆ [0, 1/2]. -/
def majOk (A B : Nat) : Bool :=
  let m : Rat := ((A + B : Nat) : Rat) / 33554432
  let r : Rat := ((B - A : Nat) : Rat) / 33554432
  let sc := sinCosPiQ (m / 30)
  decide (A ≤ B) && decide (B ≤ 8388608) && decide (0 < (QI.smul (5 / 4) sinA).lo) &&
    majCore sc (sc.2.lo * sc64).floor (sc.1.lo * sc64).floor m r

def majChainOk : List Nat → Bool
  | a :: b :: rest => majOk a b && majChainOk (b :: rest)
  | _ => true

theorem majChainOk_cons {a b : Nat} {rest : List Nat} (h : majOk a b = true)
    (h' : majChainOk (b :: rest) = true) : majChainOk (a :: b :: rest) = true := by
  show (majOk a b && majChainOk (b :: rest)) = true
  rw [h, h']; rfl

theorem majChainOk_single (a : Nat) : majChainOk [a] = true := rfl

end ZetaS.MajCheck

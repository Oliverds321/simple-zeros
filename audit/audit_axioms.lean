/-
audit_axioms.lean — the axiom gate for the `Zeta23`-side layers `ZetaQ` builds on.

Every declaration below must report exactly the three standard Lean axioms

    [propext, Classical.choice, Quot.sound]

which is [R]'s own standard (`comparator/PrintAxioms/`). Any extra axiom, and in
particular any `sorryAx`, is a gate failure.

Run from the project root, AFTER a green `lake build`:
    lake env lean audit/audit_axioms.lean
-/
import Zeta23

-- Step 1 — the class swap.
#print axioms Zeta23.Params.Valid.validQ

-- Step 2 — the free-buffer window layer and H1's certificate at a free buffer.
#print axioms Zeta23.Assembly.count_certificate_free
#print axioms Zeta23.Assembly.s1D_le

-- Step 3 — the Gevrey tail chain at free D₀ (QT.a, QT.b(1)–(5), the NII mirror,
-- and the QT.a ⟹ QT.b bridge).
#print axioms Zeta23.Taper.norm_paperFT_le_gevrey
#print axioms Zeta23.Params.norm_phiHat_le_gevrey
#print axioms Zeta23.Tail.TailHypG.tailInputsD
#print axioms Zeta23.Tail.TailHypG.of_profile
#print axioms Zeta23.Tail.NIID_le

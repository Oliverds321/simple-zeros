"""Receipt: the Lean design taper was [R]'s FLAT plateau, while kappa_C = 2 - 0.7212835668 is
the OPTIMAL-PROFILE constant.  Uses only the paper's own solver, `fb.py`.

`fb.py` is the authoring project's numerical helper and is NOT part of this repository, so
this script cannot be re-run from a clean checkout; it is kept as the record of how the
finding was established, and the recorded output is `flat_vs_profile_receipt.out` beside it.
To re-run, set ZETAQ_KIT_SCRIPTS to the directory holding `fb.py`."""
import math, sys, os
_HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get(
    "ZETAQ_KIT_SCRIPTS",
    os.path.join(_HERE, os.pardir, os.pardir, "kit", "repo_v1", "scripts")))
import fb
import numpy as np
for name, C, lam, kappa in (("q<=Q (Thm 1)", math.pi**4/18, 1.2507321515, 2-0.7212835668),
                             ("dyadic (Cor 2)", 2*math.pi**4/27, 1.1931581210, 2-0.7099167448)):
    opt = fb.payoff_a(C)
    Bf = fb.flat_v_payoff(C, lam)
    lams = np.linspace(1.0, 1.3, 301)
    Bbest, lbest = min((fb.flat_v_payoff(C, l), l) for l in lams)
    print(f"[{name}]  optimal profile: lam*={opt['lam']:.10f} B={opt['B']:.10f} P={opt['P']:.10f}")
    print(f"[{name}]  FLAT taper at lam*={lam}: B={Bf:.10f} P={2-Bf:.10f}   (tree's kappa_C={kappa:.10f}; gap={Bf-kappa:+.4f})")
    print(f"[{name}]  FLAT taper, best lam in [1,1.3]: lam={lbest:.4f} B={Bbest:.10f} P={2-Bbest:.10f}")

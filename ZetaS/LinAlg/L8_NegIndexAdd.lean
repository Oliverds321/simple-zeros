/-
Node L8 (track L) — subadditivity of the negative index, used in lem:sigd-removal (b) (l.1214–1215: "n_± are
subadditive (Weyl)"). Mirror of trunk `RHLinalg.posIndex_add_le` (Inertia.lean:90), by negation.

Proof (L2_1): `n₋(A) = n₊(−A)` (`SpecHelpers.negIndex_eq_posIndex_neg`: `−A = U·diag(−λ)·U*`, so the eigenvalue
multiset of `−A` is `{−λᵢ}`, via characteristic polynomials), `−(Q₁+Q₂) = (−Q₁) + (−Q₂)`, and trunk `posIndex_add_le`.
-/
import ZetaS.Interfaces
import Zeta23.LinAlg.Inertia
import ZetaS.LinAlg.SpecHelpers

open RHLinalg

namespace ZetaS

theorem negIndex_add_le {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    {Q₁ Q₂ : Matrix n n 𝕜} (hQ₁ : Q₁.IsHermitian) (hQ₂ : Q₂.IsHermitian) :
    negIndex (hQ₁.add hQ₂) ≤ negIndex hQ₁ + negIndex hQ₂ := by
  rw [negIndex_eq_posIndex_neg, negIndex_eq_posIndex_neg hQ₁, negIndex_eq_posIndex_neg hQ₂,
    posIndex_congr (neg_add Q₁ Q₂) _ (hQ₁.neg.add hQ₂.neg)]
  exact posIndex_add_le hQ₁.neg hQ₂.neg

end ZetaS

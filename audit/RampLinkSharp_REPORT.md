# The SHARP §11 ramp link — receipt for `ZetaQ/RampLinkSharp.lean` (imports ZetaQ.RampLink, DesignProfile, Budget; sorry-free, kernel-clean)

Headline: `rampSharpK : Family → ℝ | qle => 85/100 | dyadic => 107/100` and
  profileRampLink_sharp (F P) (hP : P.Valid) (hprof : P.prof = F.designProfile) (hlam : P.lam = F.lamStar) (hwL : 100 w ≤ LL) :
    B F.Cconst (vDesign P) ≤ B F.Cconst (vProfile P) + rampSharpK F * (w/LB)
  profileRampLink_design (hdes : DesignOfRecord F r ε Q P) (hr : 3 ≤ r) (hLL : 100 ≤ LL) : … + rampSharpK F * (w/LB)
  profileRampLink_design_three : … + 3·(w/LB);   profileRampLink_design_L₃ : … + L₃ P   (inside the budget's ramp row 6w/L)
Crude fallbacks (no far-mass refinement): K = 3.0 (qle), 4.7 (dyadic).
Route (exact, no Lipschitz): with c := profMass/(λa) ≥ 1 and u := c·vProfile − vDesign = 1_core·p²(1−ramp²)/(λa) ≥ 0,
  B(v_design) − B(v_profile) = (c²−1)B(v′) − c[Q(v′,u)+Q(u,v′)] + Q(u,u) ≤ (c²−1)B(v′) + (s₀/(λa))(c−1) + (1+C)λ(c−1)²
(`B_sub_B_le_quad`, generic); strip bound `prof_sq_le_edge` (p(t)² ≤ p(λ/2 − 1/100)² = s₀: 0.0643 qle / 0.086 dyadic);
`profMass_sub_le_of_strip` (profMass − λa ≤ 2(w/ℒ)s₀); kernel far-mass bound `W_mul_le_far`, `B_vProfile_le_refined`
(B(v′) ≤ 1/profMass + 1 + Cλm², m = far mass 0.272 / 0.208). Numbers: profMass 0.9796/0.9566, η ≤ 0.1315/0.1802·(w/ℒ),
B(v′) ≤ 2.52/2.42, K′ = 0.675/0.8925 (w/ℒ), K_F = λ*K′ = 0.85/1.07 (w/L). True cost ≈ 10⁻³ w/L would need a lower bound on
(W⋆v′) on the strips — unnecessary. Note: `DesignOfRecord` gives w = 1 via r ≥ 3 (`w_eq_one_of_design`); `100 ≤ LL` is an
explicit hypothesis (from Qn ≥ e^100 via `LL_ge_log_of_design`).

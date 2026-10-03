/-
Node SD-A3 (L7_7, F1a): the two window-moment floors `Valid.a_ge`, `Valid.b_ge` at the S53-L75 design point, in the
EVENTUAL form (`ℒ ≥ 2.5·10⁵`, `w = 1`). Draft: ssec:shell-cert-53 (`a = ⟨p²⟩ = 0.7500002`, `b = 0.6240`); paper §2.2.
Lead's ruling (L7_4 correction 1): the floor 3/4 is KEPT; the degree-12 profile meets it only for `ℒ/w ≥ 2.0273·10⁵`.
PROOF (round 2): `ZetaQ.design_moments_of'` (`DesignProfile.lean:763`, profile-generic) at
`κ = (λ/2)·x`, `x = 219999/220000` (so `κ ≤ λ/2 − 1/ℒ` needs `ℒ ≥ 230 366`), with the EXACT integral
`∫_{−κ}^{κ} p² = (λ/2)(G(x) − G(−x))`, `G(y) = Σ_k e_k y^{2k+1}/(2k+1)`, `Σ_k e_k y^{2k} = q(y)²`, `p(t) = q(2t/λ)`;
`G(x) − G(−x) − (3/4)·2 = 2(J − 3/4)`, `J − 3/4 = 2.40·10⁻⁸ > 0` (`gen_A3.py`), and `(2J − x) − 1/2 = 4.6·10⁻⁶ > 0`.
Deps: SD-A1, SD-A2. Difficulty M.
-/
import ZetaShell.Design.SD_A2_ProfileQ

namespace ZetaShell.Design

open ZetaQ

/-- the S53-L75 profile in the variable `y = 2t/λ`. -/
noncomputable def q53 (y : ℝ) : ℝ := (1 : ℝ) + (-109245641 / 315967035 : ℝ) * y ^ 2 + (-484609675 / 903872491 : ℝ) * y ^ 4 + (1126440115 / 499347366 : ℝ) * y ^ 6 + (-1244916364 / 475100341 : ℝ) * y ^ 8 + (381673291 / 981251350 : ℝ) * y ^ 10 + (37853428 / 698475165 : ℝ) * y ^ 12

/-- an antiderivative of `q53²`. -/
noncomputable def G53 (y : ℝ) : ℝ := (1 : ℝ) * y ^ 1 + (-218491282 / 947901105 : ℝ) * y ^ 3 + (-85974810127346160381039179 / 451191306362567547042957375 : ℝ) * y ^ 5 + (23209375588006950850047955 / 33275799014069722374484899 : ℝ) * y ^ 7 + (-39887020064390144688686045567108024044334386 / 55117146804537540564345801838100431351393809 : ℝ) * y ^ 9 + (63149759957771609302523254932498577312424 / 4062912755365699782182591383784033400644075 : ℝ) * y ^ 11 + (1993669539828183191417030902037690969529346696429524212793683 / 3349437603519014896405902961133726869210480518645778787515500 : ℝ) * y ^ 13 + (-1900303844692334048858137059277511759277888024324647 / 2321872083151086919664004199295016316811221138825125 : ℝ) * y ^ 15 + (1328672908332181045750011757844365486874832687857031 / 2637838851185338896846366127850211631405546724778190 : ℝ) * y ^ 17 + (-14584581729698543908845651476201336 / 154469573337554453787314196643547175 : ℝ) * y ^ 19 + (-8481258352521928617832401188999707 / 1341980285944668355068634477942942500 : ℝ) * y ^ 21 + (14447642440391548 / 7881866533873811625 : ℝ) * y ^ 23 + (1432882011351184 / 12196688903044430625 : ℝ) * y ^ 25

theorem S53_p_eq (t : ℝ) : S53L75.p t = q53 (200 * t / 191) := by
  show (∑ i : Fin 7, ((S53L75.d.get i : ℚ) : ℝ) * (2 * t / ((S53L75.lam : ℚ) : ℝ)) ^ (2 * (i : ℕ)))
    = q53 (200 * t / 191)
  simp [Fin.sum_univ_succ, S53L75, q53]
  ring

theorem hasDerivAt_G53 (y : ℝ) : HasDerivAt G53 (q53 y ^ 2) y := by
  have h0 := (hasDerivAt_pow 1 y).const_mul (1 : ℝ)
  have h1 := (hasDerivAt_pow 3 y).const_mul (-218491282 / 947901105 : ℝ)
  have h2 := (hasDerivAt_pow 5 y).const_mul (-85974810127346160381039179 / 451191306362567547042957375 : ℝ)
  have h3 := (hasDerivAt_pow 7 y).const_mul (23209375588006950850047955 / 33275799014069722374484899 : ℝ)
  have h4 := (hasDerivAt_pow 9 y).const_mul (-39887020064390144688686045567108024044334386 / 55117146804537540564345801838100431351393809 : ℝ)
  have h5 := (hasDerivAt_pow 11 y).const_mul (63149759957771609302523254932498577312424 / 4062912755365699782182591383784033400644075 : ℝ)
  have h6 := (hasDerivAt_pow 13 y).const_mul (1993669539828183191417030902037690969529346696429524212793683 / 3349437603519014896405902961133726869210480518645778787515500 : ℝ)
  have h7 := (hasDerivAt_pow 15 y).const_mul (-1900303844692334048858137059277511759277888024324647 / 2321872083151086919664004199295016316811221138825125 : ℝ)
  have h8 := (hasDerivAt_pow 17 y).const_mul (1328672908332181045750011757844365486874832687857031 / 2637838851185338896846366127850211631405546724778190 : ℝ)
  have h9 := (hasDerivAt_pow 19 y).const_mul (-14584581729698543908845651476201336 / 154469573337554453787314196643547175 : ℝ)
  have h10 := (hasDerivAt_pow 21 y).const_mul (-8481258352521928617832401188999707 / 1341980285944668355068634477942942500 : ℝ)
  have h11 := (hasDerivAt_pow 23 y).const_mul (14447642440391548 / 7881866533873811625 : ℝ)
  have h12 := (hasDerivAt_pow 25 y).const_mul (1432882011351184 / 12196688903044430625 : ℝ)
  have h := ((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12)
  have e : G53 = fun y => (1 : ℝ) * y ^ 1 + (-218491282 / 947901105 : ℝ) * y ^ 3 + (-85974810127346160381039179 / 451191306362567547042957375 : ℝ) * y ^ 5 + (23209375588006950850047955 / 33275799014069722374484899 : ℝ) * y ^ 7 + (-39887020064390144688686045567108024044334386 / 55117146804537540564345801838100431351393809 : ℝ) * y ^ 9 + (63149759957771609302523254932498577312424 / 4062912755365699782182591383784033400644075 : ℝ) * y ^ 11 + (1993669539828183191417030902037690969529346696429524212793683 / 3349437603519014896405902961133726869210480518645778787515500 : ℝ) * y ^ 13 + (-1900303844692334048858137059277511759277888024324647 / 2321872083151086919664004199295016316811221138825125 : ℝ) * y ^ 15 + (1328672908332181045750011757844365486874832687857031 / 2637838851185338896846366127850211631405546724778190 : ℝ) * y ^ 17 + (-14584581729698543908845651476201336 / 154469573337554453787314196643547175 : ℝ) * y ^ 19 + (-8481258352521928617832401188999707 / 1341980285944668355068634477942942500 : ℝ) * y ^ 21 + (14447642440391548 / 7881866533873811625 : ℝ) * y ^ 23 + (1432882011351184 / 12196688903044430625 : ℝ) * y ^ 25 := by funext y; rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold q53
  push_cast
  ring

theorem integral_S53_sq (a b : ℝ) :
    ∫ t in a..b, (S53L75.p t) ^ 2 = 191 / 200 * (G53 (200 * b / 191) - G53 (200 * a / 191)) := by
  have hF : ∀ t : ℝ, HasDerivAt (fun t => 191 / 200 * G53 (200 * t / 191)) ((S53L75.p t) ^ 2) t := by
    intro t
    have hlin : HasDerivAt (fun t : ℝ => 200 * t / 191) (200 * 1 / 191) t :=
      ((hasDerivAt_id t).const_mul (200 : ℝ)).div_const 191
    have hc := ((hasDerivAt_G53 (200 * t / 191)).comp t hlin).const_mul (191 / 200 : ℝ)
    refine hc.congr_deriv ?_
    rw [S53_p_eq]; ring
  have hcont : Continuous fun t : ℝ => (S53L75.p t) ^ 2 := by
    have e : (fun t : ℝ => (S53L75.p t) ^ 2) = fun t => q53 (200 * t / 191) ^ 2 := by
      funext t; rw [S53_p_eq]
    rw [e]; unfold q53; fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t) (hcont.intervalIntegrable _ _)]
  ring

theorem moments_S53_eventual (P : ParamsQ) (hprof : P.prof = S53L75.poly)
    (hlam : P.lam = (S53L75.lam : ℝ)) (hϱ : P.ϱ = Zeta23.Taper.rhoTwo) (hw : P.w = 1)
    (hl : Zeta23.l P.T ≠ 0) (hLL : 250000 ≤ P.LL) :
    3 / 4 ≤ P.aQ ∧ 1 / 2 ≤ P.bQ := by
  have hlamR : P.lam = 191 / 100 := by rw [hlam]; norm_num [S53L75]
  have heven : ∀ t, P.prof.eval (-t) = P.prof.eval t := by
    rw [hprof]; exact S53L75.poly_eval_neg
  have hval : ∫ t in (-(191 / 200 * (219999 / 220000 : ℝ)))..(191 / 200 * (219999 / 220000 : ℝ)),
      (P.prof.eval t) ^ 2
      = 191 / 200 * (G53 (200 * (191 / 200 * (219999 / 220000 : ℝ)) / 191)
          - G53 (200 * (-(191 / 200 * (219999 / 220000 : ℝ))) / 191)) := by
    simp_rw [hprof, ShellProfile.poly_eval]
    exact integral_S53_sq _ _
  have hLB : P.LB = 191 / 100 * P.LL := by unfold ParamsQ.LB; rw [hlamR]
  refine design_moments_of' P heven hval (by rw [hϱ]; exact Zeta23.Taper.rhoTwo_taper) hl hw
    (by linarith) (by rw [hLB]; linarith) (by norm_num) ?_ ?_ ?_
  · rw [le_div_iff₀ (by linarith), hLB]
    nlinarith
  · rw [hlamR]; norm_num [G53]
  · rw [hlamR]; norm_num [G53]

end ZetaShell.Design

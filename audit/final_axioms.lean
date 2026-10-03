import ZetaQ
-- The six headline theorems (`ZetaQ/Margin.lean`, namespace `ZetaQ.JoinProved`).
-- Expected since the Gallagher rethread: `[propext, Classical.choice, Quot.sound]` for each.
#print axioms ZetaQ.JoinProved.theorem_one_generic_proved'
#print axioms ZetaQ.JoinProved.corollary_two_dyadic_proved'
#print axioms ZetaQ.JoinProved.corollary_three_even_qQ_proved'
#print axioms ZetaQ.JoinProved.corollary_three_odd_qQ_proved'
#print axioms ZetaQ.JoinProved.corollary_three_even_dyadic_proved'
#print axioms ZetaQ.JoinProved.corollary_three_odd_dyadic_proved'
-- The headline route (as before).
#print axioms ZetaQ.HFrob.hfrob_qle_of_sep
#print axioms ZetaQ.exists_designOfRecordM
#print axioms ZetaQ.Cor3.EvenFamInstance.admissible_even
#print axioms ZetaQ.Cor3.EvenFamInstance.admissible_odd
#print axioms ZetaQ.Cor3.EvenFamInstance.corollary3_even_dyadic
-- Lemma 6.1 as consumed: the Gallagher sieve and the two discharged interfaces.
#print axioms ZetaQ.Gallagher.gallagher_additive_large_sieve
#print axioms ZetaQ.Gallagher.multiplicative_large_sieve_gallagher
#print axioms ZetaQ.Ends.largeSieve_holds
#print axioms ZetaQ.largeSieveFamily_holds
-- The sharp sieve, kept as a record and consumed by nothing above: still carries `sorryAx`
-- through `ZetaQ.l2_concentration_exists`.
#print axioms ZetaQ.multiplicative_large_sieve
-- Corollary 3'' inputs (branch reflected-sieve): the reflected large sieve for a parity class at
-- the Gallagher budget Q^2/2 + pi(N + 1/2), and its consumption for one parity class.
#print axioms ZetaQ.Reflected.multiplicative_large_sieve_gallagher_window
#print axioms ZetaQ.Reflected.reflected_large_sieve_gallagher
#print axioms ZetaQ.Reflected.reflected_large_sieve_parityFamily
#print axioms ZetaQ.Cor3Reflected.largeSieveParity_holds
#print axioms ZetaQ.Cor3Reflected.family_consumption_par
#print axioms ZetaQ.Cor3Reflected.family_le_diagonal_pointwise_par
#print axioms ZetaQ.Cor3Reflected.famPP_le_sieve_par
#print axioms ZetaQ.Cor3Reflected.famSieveAt_par
#print axioms ZetaQ.Cor3Reflected.famSieveAt_full
#print axioms ZetaQ.Cor3Reflected.famPP_total_leB'
#print axioms ZetaQ.Cor3Reflected.famPP_total_le_par
#print axioms ZetaQ.Cor3Reflected.famPP_le_zone_split_par
#print axioms ZetaQ.Cor3Reflected.frobenius_inzone_eventually_par
#print axioms ZetaQ.Cor3Reflected.hfrob_par_qle_of_sep
#print axioms ZetaQ.Cor3Reflected.hfrob_par_dyad_of_sep
-- Corollary 3'' headlines (branch reflected-sieve, ZetaQ/Cor3Full.lean): the four parity families
-- (the SAME zero counts as corollary_three_*_proved') at the FULL-family constants
-- 0.7212 (q <= Q) and 0.7098 (dyadic), through the reflected-sieve families Family.*R.
#print axioms ZetaQ.JoinProved.corollary_three_even_qQ_full_proved'
#print axioms ZetaQ.JoinProved.corollary_three_odd_qQ_full_proved'
#print axioms ZetaQ.JoinProved.corollary_three_even_dyadic_full_proved'
#print axioms ZetaQ.JoinProved.corollary_three_odd_dyadic_full_proved'
#print axioms ZetaQ.Cor3Full.hfrob_evenQleR_of_design
#print axioms ZetaQ.Cor3Full.hfrob_evenDyadicR_of_design
#print axioms ZetaQ.Payoff.profileRampLink_sharp_qle_twoC
#print axioms ZetaQ.Payoff.profileRampLink_sharp_dyadic_twoC
#print axioms ZetaQ.design_gevreyBprod_le_full

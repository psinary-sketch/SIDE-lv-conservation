import SIDELvConservation.T1_MellinFactorization
import SIDELvConservation.T2_SDarkness
import SIDELvConservation.T3_StepNineBridge
import SIDELvConservation.GammaBounds
import SIDELvConservation.C7OrderBounds

/-!
# Axiom audit

Run `lake env lean AxiomCheck.lean` to reproduce the `#print axioms`
output for every theorem in this kernel.

T1 and T2 are expected to reduce to Mathlib's standard axiomatic base
(`Classical.choice`, `Quot.sound`, `propext`).  T3 is expected to
additionally list `sorryAx` due to the pinned emergent-totality gap
(FINDINGS F.2026-07-09-b) — this is the intended `sorry` and its
presence is the compiler's verdict.
-/

open SIDELvConservation

-- T1
#print axioms T1_completedRiemannZeta_factors_through_mellin

-- T2
#print axioms T2a_mellin_congr_on_Ioi
#print axioms T2a'_mellin_congr
#print axioms T2b_mellin_exhaustion
#print axioms T2c_phi_side_predicates_are_s_dark
#print axioms completedRiemannZeta_eq_mellinPhi
#print axioms T2d_zero_iff_mellinPhi_zero

-- T3
#print axioms T3.T3a_zeroLoc_is_function_of_Phi
#print axioms T3.T3b_joint_witness_gives_combinations_exclude
#print axioms T3.T3_perClass_to_combinations
-- T3′ (Determination-shared-witness bridge) and T3″ (countermodel), added v0.2.0
#print axioms T3.T3prime_shared_witness
#print axioms T3.T3doubleprime_general_commutation_fails

-- W-8 (C₇-order execution): vertical-line norm bounds for the Hadamard input.
-- Expected Mathlib base only (`propext`, `Classical.choice`, `Quot.sound`), no `sorryAx`.
#print axioms Complex.norm_Gamma_le_Gamma_re            -- brick 1: ‖Γ z‖ ≤ Γ(re z)
#print axioms Complex.norm_riemannZeta_le_tsum          -- brick 2: ‖ζ s‖ ≤ ∑ 1/n^(re s)
#print axioms Complex.norm_completedZeta₀_le_of_re_eq_two -- edge bound: ‖Λ₀‖ ≤ π/6 + 3/2 on re s = 2
#print axioms Complex.norm_completedZeta₀_le_of_re_eq_neg_one -- reflected edge on re s = -1 (via FE)
#print axioms Real.Gamma_le_two_mul_rpow -- real-Γ growth (log u ≤ u-1); the classical order-1 ingredient
#print axioms SIDELvConservation.exists_norm_Phi_le -- W-8 domination: ‖Φ t‖ ≤ C·e^(-p t) on [1,∞)
#print axioms SIDELvConservation.completedRiemannZeta₀_eq_half_mellin -- brick 3: Λ₀ = ½·mellin f_modif (rfl)
#print axioms SIDELvConservation.norm_completedRiemannZeta₀_le -- brick 3: ‖Λ₀ s‖ ≤ ½·∫ t^(re(s/2)-1)‖f_modif‖
#print axioms SIDELvConservation.norm_f_modif_of_one_lt -- brick 3 gateway: ‖f_modif t‖ = |ek 0 t - 1| on Ioi 1
#print axioms SIDELvConservation.norm_f_modif_of_mem_Ioo -- brick 3 gateway: FE fold on Ioo 0 1
#print axioms SIDELvConservation.integrableOn_rpow_mul_exp_Ioi -- sub-lemma 1: scaled-Γ tail integrability

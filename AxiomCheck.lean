import SIDELvConservation.T1_MellinFactorization
import SIDELvConservation.T2_SDarkness
import SIDELvConservation.T3_StepNineBridge

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

import SIDELvConservation.PartialPositivity
import SIDELvConservation.ZeroCarrier
import SIDELvConservation.CouplingsAtPhi
import SIDELvConservation.RegisterPentagon
import SIDELvConservation.T3_StepNineBridge
import SIDELvConservation.C7FiniteTypeFalse

open SIDELvConservation

-- ============================================================
-- v0.10.0 combined #print axioms — lv deposit-relevant set.
-- W-ORD-P1-FINSET discharge + the standing deposit terminals.
-- Clean profile = [propext, Classical.choice, Quot.sound].
-- (T3.T3_perClass_to_combinations is the OPEN bracket — carries
--  the one intended sorry; excluded here by design.)
-- ============================================================

-- ---- W-ORD-P1-FINSET discharge (this version's new content) ----
#print axioms PartialPositivity.lowFinset_mem_iff
#print axioms PartialPositivity.finite_strip_box_riemannZeta_zeros

-- ---- R4 finite-range certificate (deposited terminal — must be UNMOVED) ----
#print axioms PartialPositivity.partialPositivity_finiteRange

-- ---- h1 complete at the witness (eight-coupling ledger) ----
#print axioms h1_complete_at_Phi

-- ---- register pentagon terminals ----
#print axioms RegisterPentagon.certifiedInput_not_zeroRealizing
#print axioms RegisterPentagon.R5_input_at_Phi
#print axioms RegisterPentagon.goalState_of_h1_h2
#print axioms RegisterPentagon.goalState_sevenClasses_of_h2

-- ---- the bracket (closed halves) + the finite-type countermodel ----
#print axioms T3.T3prime_shared_witness
#print axioms T3.T3doubleprime_general_commutation_fails
#print axioms C7_finite_type_false

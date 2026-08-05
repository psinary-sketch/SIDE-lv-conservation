import SIDELvConservation.LeadLaw
import SIDELvConservation.SaltCheck_LeadLaw

/-! Axiom audit for D-2a (the lead law) and its shared field layer. Prints the profile of each
terminal, including the two conversion steps that moved the row from two premises to one, and
the two salt-check witnesses. -/

#print axioms SIDELvConservation.FieldLayer.top_coeff_of_expansion
#print axioms SIDELvConservation.FieldLayer.norml_top
#print axioms SIDELvConservation.LeadLaw.v_monic
#print axioms SIDELvConservation.LeadLaw.v_natDegree
#print axioms SIDELvConservation.LeadLaw.leadingCoeff_hOf
#print axioms SIDELvConservation.LeadLaw.ptTop_eq_p_zero
#print axioms SIDELvConservation.LeadLaw.norml_top_eq_ptTop
#print axioms SIDELvConservation.LeadLaw.lead_law_of_top_coeff
#print axioms SIDELvConservation.LeadLaw.lead_law
#print axioms SIDELvConservation.SaltCheckLeadLaw.expansion_exists_of_palindromic
#print axioms SIDELvConservation.SaltCheckLeadLaw.hg_is_load_bearing

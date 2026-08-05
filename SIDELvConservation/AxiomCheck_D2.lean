import SIDELvConservation.Genus5
import SIDELvConservation.Genus5Confinement
import SIDELvConservation.TwoSidesIdentity

/-! Axiom audit for D-2b (both units, per the joint-row rule) and D-2c. -/

-- D-2b unit 1: the catalogue
#print axioms SIDELvConservation.Genus5.genus_mod_four
#print axioms SIDELvConservation.Genus5.genus_one_forces
#print axioms SIDELvConservation.Genus5.genus_five_forces
#print axioms SIDELvConservation.Genus5.classification

-- D-2b unit 2: the confinement certificates
#print axioms SIDELvConservation.Genus5Confinement.e8_confined
#print axioms SIDELvConservation.Genus5Confinement.quad_confined
#print axioms SIDELvConservation.Genus5Confinement.w16_confined
#print axioms SIDELvConservation.Genus5Confinement.golay_five_roots_in_interval
#print axioms SIDELvConservation.Genus5Confinement.golay_confined

-- D-2c: the two-sides identity instance
#print axioms SIDELvConservation.TwoSides.heine_one
#print axioms SIDELvConservation.TwoSides.heine_two
#print axioms SIDELvConservation.TwoSides.heine_three
#print axioms SIDELvConservation.TwoSides.ladder_three
#print axioms SIDELvConservation.TwoSides.two_sides_balance
#print axioms SIDELvConservation.TwoSides.heine_three_degenerate
#print axioms SIDELvConservation.TwoSides.vandermonde_square_is_load_bearing

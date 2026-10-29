/-!
# b724, (R334)(5): the negation of T3_perClass_to_combinations, on the scratch branch scratch-b724 alone

At the deposit pin v0.10.0 = 93c27ec, imported by no module; the workflow`s closure step runs this text above every module of the
target. (1) The theorem: its statement the negation of the deposit statement`s closure over its binders, proved from
`T3doubleprime_general_commutation_fails`. (2) An `example` deriving `False` from it and the deposit`s theorem, so the elaborator
checks the statement against the deposit`s own. (3) The axioms printed. (4) The statement as the text writes it, as an `example`,
printed beside.
-/

namespace SIDELvConservation
namespace T3

#check @T3_perClass_to_combinations

theorem not_T3_perClass_to_combinations :
    ¬ ∀ (𝒞 : Set Coupling) (s : ℂ), (∀ C ∈ 𝒞, PerClassExcludes C s) → CombinationsExclude 𝒞 s :=
  fun h => T3doubleprime_general_commutation_fails (fun 𝒞 s hp => h 𝒞 s hp)

example : False := not_T3_perClass_to_combinations T3_perClass_to_combinations

end T3
end SIDELvConservation

#print axioms SIDELvConservation.T3.not_T3_perClass_to_combinations
#print axioms SIDELvConservation.T3.T3doubleprime_general_commutation_fails
#print axioms SIDELvConservation.T3.T3_perClass_to_combinations

namespace SIDELvConservation
namespace T3

example : ¬ T3_perClass_to_combinations := T3doubleprime_general_commutation_fails

end T3
end SIDELvConservation

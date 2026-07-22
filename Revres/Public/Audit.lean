import Revres.Public.MainTheorem

/-!
# Public theorem audit

Run `lake env lean Revres/Public/Audit.lean` to check the public API and its
trusted footprint.
-/

#check Revres.Public.HardFormula
#check Revres.Public.FormulaBitSize
#check Revres.Public.Refutation
#check Revres.Public.LowerBound
#check Revres.Public.hard_family_properties
#check Revres.Public.stretched_exponential_lower_bound
#check Revres.Public.superpolynomial_lower_bound

#print axioms Revres.Public.hard_family_properties
#print axioms Revres.Public.stretched_exponential_lower_bound
#print axioms Revres.Public.superpolynomial_lower_bound
#print axioms Revres.subsequencePathFamilyHardness
#print axioms Revres.subsequence_revres_lower_bound_unconditional
#print axioms Revres.subsequence_revres_superpolynomial_unconditional

/-
  CCH Final Verification
  ======================
  Verifies the headline theorems of the CCH Trilemma project.
  Each CCH_* file imports only Mathlib (no cross-file dependencies),
  so they are independently checkable. The master file packages the
  three-corner trilemma; here we just import it and print axioms.
-/

import CCHProofs.CCH_MasterTrilemma

-- Check the master theorem
#check @CCH.cch_master_trilemma
#check @CCH.cch_corner_UC
#check @CCH.cch_corner_UT
#check @CCH.cch_corner_CT
#check @CCH.cch_at_most_two

-- Print axioms — should be only [propext, Classical.choice, Quot.sound]
#print axioms CCH.cch_master_trilemma
#print axioms CCH.cch_corner_UC
#print axioms CCH.cch_corner_UT
#print axioms CCH.cch_corner_CT
#print axioms CCH.cch_at_most_two

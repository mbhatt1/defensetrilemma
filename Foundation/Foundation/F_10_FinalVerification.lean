/-
  Foundation Final Verification
  =============================
  Verifies the master foundation theorem and its concrete instances.
-/

import Foundation.F_10_MasterFoundation

-- Check the master theorem
#check @Foundation.master_foundation_theorem
#check @Foundation.mirror_trilemma_instance
#check @Foundation.rice_instance
#check @Foundation.nat_succ_instance
#check @Foundation.spec_bound_instance
#check @Foundation.unification_statement

-- Print axioms — should be only [propext, Classical.choice, Quot.sound]
-- or fewer.
#print axioms Foundation.master_foundation_theorem
#print axioms Foundation.mirror_trilemma_instance
#print axioms Foundation.rice_instance
#print axioms Foundation.nat_succ_instance
#print axioms Foundation.unification_statement

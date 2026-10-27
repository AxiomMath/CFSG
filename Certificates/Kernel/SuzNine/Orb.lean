module

public import Certificates.Kernel.SuzNine.OrbData
public import Certificates.Kernel.SuzNine.Chk
public import Certificates.Data.Kernel.SuzNine.Orb
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelSuzNine

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.SuzNine

@[expose] noncomputable def GA (j : Nat) : Nat :=
  CertificateChecks.KernelSpor.SuzInvT1.F
    (Bool.rec (motive := fun _ => Nat) (Nat.sub j 9) (Nat.add 18 j) (Nat.blt j 10))

theorem x0_tree : allN 45 (treeAt (setK 6) (listKey X0L) HG 10 X0E X0PA) = true := by quickRfl
theorem x0_tree_a : allN 45 (treeAt (setK 6) (listKey X0L) GA 16 X0E X0PA) = true := by quickRfl
theorem x0_sort : allN 45 (sortAt 45 X0E X0SG) = true := by quickRfl
theorem x0_cm : allN 45 (closedAt (setK 6) HG 10 45 X0E X0CM) = true := by quickRfl
theorem x0_ca : allN 45 (closedAt (setK 6) GA 16 45 X0E X0CA) = true := by quickRfl
theorem x0_moved : allN 45 (movedAt 6 X0E UGT) = true := by quickRfl

theorem x3_tree : allN 135 (treeAt (setK 4) (listKey X3L) HG 10 X3E X3PA) = true := by quickRfl
theorem x3_tree_a : allN 135 (treeAt (setK 4) (listKey X3L) GA 16 X3E X3PA) = true := by quickRfl
theorem x3_sort : allN 135 (sortAt 135 X3E X3SG) = true := by quickRfl
theorem x3_cm : allN 135 (closedAt (setK 4) HG 10 135 X3E X3CM) = true := by quickRfl
theorem x3_ca : allN 135 (closedAt (setK 4) GA 16 135 X3E X3CA) = true := by quickRfl
theorem x3_moved : allN 135 (movedAt 4 X3E UGT) = true := by quickRfl

end CertificateChecks.KernelSuzNine

end

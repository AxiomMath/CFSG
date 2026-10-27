module

public import Certificates.Kernel.Misc.Perm.U33B.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33B

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.U33B CFSG.KC.LQT.P

theorem treeB : allN 216 (treeAt (mul 28) (one 28) KG 2 E PA) = true := by decide +kernel
theorem sortB : allN 216 (sortAt 216 E SG) = true := by decide +kernel
theorem closedB : allN 216 (closedAt (mul 28) KG 2 216 E CT) = true := by decide +kernel
theorem cubeB : allN 216 (cubeMulAt E 216) = true := by decide +kernel
theorem smallB : allN 216 (smallAt E 216 (E iz)) = true := by decide +kernel
theorem cnt3 : Nat.beq (cntN 216 cubeAt) 27 = true := by decide +kernel
theorem zB : zOK (E iz) (E ixx) (E iyy) = true := by decide +kernel
theorem twB : allN 28 (wordAt 28 AG 2 TW T) = true := by decide +kernel
theorem kwB : allN 2 (wordAt 28 AG 2 KW KG) = true := by decide +kernel
theorem coverB : allN 28 (coverAt 28 AG 2 28 T 216 E IX) = true := by decide +kernel
theorem fixB : allN 28 (fun j => impB (Nat.blt 0 j) (notB (Nat.beq (img (T j) 0) 0))) = true := by
  decide +kernel
theorem kfixB : allN 2 (fun j => Nat.beq (img (KG j) 0) 0) = true := by decide +kernel
theorem t0B : Nat.beq (T 0) (one 28) = true := by decide +kernel

end CertificateChecks.KernelMisc.U33B

end

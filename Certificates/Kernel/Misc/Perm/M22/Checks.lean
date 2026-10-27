module

public import Certificates.Kernel.Misc.Perm.M22.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M22

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.LQT.P

theorem treeB : allN 20160 (treeAt (mul 22) (one 22) KG 2 E PA) = true := by decide +kernel
theorem sortB : allN 20160 (sortAt 20160 E SG) = true := by decide +kernel
theorem closedB : allN 20160 (closedAt (mul 22) KG 2 20160 E CT) = true := by decide +kernel
theorem badB : allN 20160 badAt = true := by decide +kernel
theorem twB : allN 22 (wordAt 22 AG 2 TW T) = true := by decide +kernel
theorem kwB : allN 2 (wordAt 22 AG 2 KW KG) = true := by decide +kernel
theorem coverB : allN 22 (coverAt 22 AG 2 22 T 20160 E IX) = true := by decide +kernel
theorem fixB : allN 22 (fun j => impB (Nat.blt 0 j) (notB (Nat.beq (img (T j) 0) 0))) = true := by
  decide +kernel
theorem kfixB : allN 2 (fun j => Nat.beq (img (KG j) 0) 0) = true := by decide +kernel
theorem t0B : Nat.beq (T 0) (one 22) = true := by decide +kernel

end CertificateChecks.KernelMisc.M22

end

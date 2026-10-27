module

public import Certificates.Kernel.Misc.Perm.U33B.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.U33B.Neg

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.U33B
open CertificateChecks.KernelMisc.U33B

@[expose] noncomputable def E5 (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (E k) (E 7) (Nat.beq k 5)

@[expose] noncomputable def IX1 (i : Nat) : Nat := IX (Nat.succ i)

theorem tree_dup : notB (allN 216 (treeAt (mul 28) (one 28) KG 2 E5 PA)) = true := by
  decide +kernel
theorem sort_dup : notB (allN 216 (sortAt 216 E5 SG)) = true := by decide +kernel
theorem closed_short : notB (allN 215 (closedAt (mul 28) KG 2 215 E CT)) = true := by
  decide +kernel
theorem cover_bad : notB (allN 28 (coverAt 28 AG 2 28 T 216 E IX1)) = true := by decide +kernel
theorem z_one : notB (zOK (one 28) (E ixx) (E iyy)) = true := by decide +kernel

end CertificateChecks.KernelMisc.U33B.Neg

end

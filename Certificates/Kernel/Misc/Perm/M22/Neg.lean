module

public import Certificates.Kernel.Misc.Perm.M22.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.M22.Neg

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CertificateChecks.KernelMisc.M22

@[expose] noncomputable def E5 (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (E k) (E 7) (Nat.beq k 5)

@[expose] noncomputable def CT10 (i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (CT i) (Nat.succ (CT i)) (Nat.beq i 10)

@[expose] noncomputable def IX1 (i : Nat) : Nat := IX (Nat.succ i)

theorem tree_dup : notB (allR 0 2016 (treeAt (mul 22) (one 22) KG 2 E5 PA)) = true := by quickRfl
theorem sort_dup : notB (allN 20160 (sortAt 20160 E5 SG)) = true := by quickRfl
theorem closed_bad : notB (allR 0 2016 (closedAt (mul 22) KG 2 20160 E CT10)) = true := by quickRfl
theorem cover_bad : notB (allN 22 (coverAt 22 AG 2 22 T 20160 E IX1)) = true := by quickRfl
theorem bad_empty : notB (noBadK xC yC WC [] (one 22)) = true := by quickRfl

end CertificateChecks.KernelMisc.M22.Neg

end

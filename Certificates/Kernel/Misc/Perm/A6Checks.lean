module

public import Certificates.Kernel.Misc.Perm.A6Data
public import Certificates.Kernel.Misc.Perm.A6Tabs
public import Certificates.Data.Kernel.Misc.PermA6
public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Misc.PermM22
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.A6

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.A6 CFSG.KC.LQT.P

@[expose] noncomputable def G (a : Nat) : Nat := nthL genL a

@[expose] noncomputable def YJ (j : Nat) : Nat := Nat.rec (motive := fun _ => Nat) Y0 (fun _ _ => Y1) j

@[expose] noncomputable def W (j k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nthL WL0 k) (fun _ _ => nthL WL1 k) j

theorem treeB : allN 360 (treeAt (mul 6) (one 6) G 2 E PA) = true := by quickRfl
theorem sortB : allN 360 (sortAt 360 E SG) = true := by quickRfl
theorem closedB : allN 360 (closedAt (mul 6) G 2 360 E CT) = true := by quickRfl

theorem evenB : andB (even 6 (G 0)) (even 6 (G 1)) = true := by quickRfl

theorem d1B : allN 2 (fun j => d1K (YJ j) (W j)) = true := by quickRfl

theorem d2B : allN 2 (fun j => allN 3 fun m =>
    d2K (YJ j) (W j (3 * m)) (W j (3 * m + 1)) (W j (3 * m + 2))) = true := by quickRfl

end CertificateChecks.KernelMisc.A6

end

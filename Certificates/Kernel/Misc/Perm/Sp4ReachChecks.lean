module

public import Certificates.Kernel.Misc.Perm.Sp4ReachTabs
public import Certificates.Data.Kernel.Misc.PermDepth
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.Sp4Reach

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.LQT.P

@[expose] noncomputable def G (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 172064833 (fun _ _ => 67275905) j

theorem treeB : allN 360 (treeAt (mul 6) (one 6) G 2 E PA) = true := by quickRfl
theorem sortB : allN 360 (sortAt 360 E SG) = true := by quickRfl
theorem depthB : allN 360 (depthAt PA D 14) = true := by quickRfl

end CertificateChecks.KernelMisc.Sp4Reach

end

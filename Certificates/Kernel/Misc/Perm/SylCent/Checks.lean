module

public import Certificates.Kernel.Misc.Perm.SylCent.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.SylCent

open CFSG.KC.Ord CFSG.KS CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW CFSG.KC.Misc.Cent
open CFSG.KC.LQT.P (allN)
open CFSG.KC.Enum (pcomp pidn)

theorem pwB : allN 4 (wWordAt 42 6 GC 3 PW PC) = true := by decide +kernel
theorem treeB : allN 64 (treeAt (pcomp 42 6 (mask 6)) (pidn 42 6) PC 4 E PA) = true := by
  decide +kernel
theorem sortB : allN 64 (sortAt 64 E SG) = true := by decide +kernel
theorem closedB : allN 64 (closedAt (pcomp 42 6 (mask 6)) PC 4 64 E CT) = true := by
  decide +kernel
theorem uwB : allN 42 (wWordAt 42 6 PC 4 UW UU) = true := by decide +kernel
theorem covB : covOK 42 6 6 RR OO UU = true := by decide +kernel
theorem orbB : allN 6 (orbOK 42 6 PC 4 RR OO) = true := by decide +kernel
theorem dfsB : centDfs 42 6 PC 4 6 OO UU leaf = true := by decide +kernel
theorem gpresB : allN 6 (fun j => presE 42 6 AA (GC j)) = true := by decide +kernel

end CertificateChecks.KernelMisc.SylCent

end

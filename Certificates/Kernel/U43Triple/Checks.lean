module

public import Certificates.Kernel.U43Triple.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU43T

open CFSG.KC.Ord CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.Clos CFSG.KC.Misc.ClosW
  CFSG.KC.Misc.InvCls

theorem invA : CFSG.KC.LQT.P.allN 3 (fun i =>
    andB (sqIdK 820 10 (mask 10) 8200 (pidn 820 10) (A i))
      (neIdK 820 10 (mask 10) 8200 (pidn 820 10) (A i))) = true := by
  decide +kernel

theorem genD : CFSG.KC.LQT.P.allN 3 (wWordAt 820 10 X 2 DW A) = true := by decide +kernel

theorem genX : CFSG.KC.LQT.P.allN 2 (wWordAt 820 10 A 3 XW X) = true := by decide +kernel

theorem genG : CFSG.KC.LQT.P.allN 3 (wWordAt 820 10 A 3 GW G) = true := by decide +kernel

theorem treeT : CFSG.KC.LQT.P.allN 128 (treeAt (pcomp 820 10 (mask 10)) (pidn 820 10) G 3 E PA) =
    true := by
  decide +kernel

theorem sortT : CFSG.KC.LQT.P.allN 128 (sortAt 128 E SG) = true := by decide +kernel

theorem closedT : CFSG.KC.LQT.P.allN 128 (closedAt (pcomp 820 10 (mask 10)) G 3 128 E CT) =
    true := by
  decide +kernel

end CertificateChecks.KernelU43T

end

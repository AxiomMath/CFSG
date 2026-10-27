module

public import Certificates.Kernel.SmithEK.EData

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem c21265pts : c8PtsK (cs.L.getD 0 []) (cs.L.getD 1 []) c8c.Q = true := by
  decide +kernel

theorem c21265fix : c8FixK (cs.L.getD 0 []) (cs.L.getD 1 []) = true := by
  decide +kernel

theorem c21265restr : c8RestrK (cs.L.getD 0 []) (cs.L.getD 1 []) (c8R c8c.Q) cs.L 0 = true := by
  decide +kernel

theorem c21265irr : c8IrrK (cs.L.getD 0 []) c8c.Q = true := by
  decide +kernel

theorem c21265rig : c8RigK (cs.L.getD 0 []) c8c.S = true := by
  decide +kernel

theorem c21265rig2 : c8Rig2K (cs.L.getD 0 []) cs.L = true := by
  decide +kernel

theorem c21265neg_pts : c8PtsK (cs.L.getD 0 []) (cs.L.getD 1 []) (c8c.Q.set 3 (cs.L.getD 1 [])) =
    false := by
  decide +kernel

theorem c21265neg_fix : c8FixK (cs.L.getD 0 []) (cs.L.getD 0 []) = false := by
  decide +kernel

theorem c21265neg_restr : c8RestrK (cs.L.getD 0 []) (cs.L.getD 1 [])
    (c8R (c8c.Q.set 7 (c8c.Q.getD 8 []))) cs.L 0 = false := by
  decide +kernel

theorem c21265neg_irr : c8IrrK (cs.L.getD 0 []) (c8c.Q.set 1 (c8c.Q.getD 2 [])) = false := by
  decide +kernel

theorem c21265neg_rig : c8RigK (cs.L.getD 0 []) (c8c.S.take 1) = false := by
  decide +kernel

theorem c21265neg_rig2 : c8Rig2K (cs.L.getD 1 []) cs.L = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK

module

public import Certificates.Kernel.L52Insp443.Data
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def ch725109o (z : Nat) : Bool :=
  orbOK (D.zB.getD z []) (D.oZ.getD z []) (normP (D.zS.getD z []) (D.zB.getD z []))
    (D.gs.getD 0 0) (D.gis.getD 0 0) (D.gs.getD 1 0) (D.gis.getD 1 0)

@[expose] noncomputable def ch725109p (w : Nat) : Bool :=
  orbOK (List.append (D.a0B.getD w []) (D.a1B.getD w [])) (D.oW.getD w [])
    (permP (D.aB.getD w []) (D.aS.getD w []))
    (D.gs.getD 0 0) (D.gis.getD 0 0) (D.gs.getD 1 0) (D.gis.getD 1 0)

#kc_each ch725109o 0 7
#kc_each ch725109p 0 2

end CertificateChecks.KernelL52I

end

module

public import Certificates.Kernel.L52Insp443.Data
public import Certificates.Kernel.L52Insp443.IrrData
public import Certificates.Data.Kernel.L52Insp443.Sub
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def wC (w : Nat) : List Nat := List.append (D.a0B.getD w []) (D.a1B.getD w [])

@[expose] noncomputable def ch725109sz (z : Nat) : Bool := subKOK (D.zB.getD z []) (D.zB.getD z [])

@[expose] noncomputable def ch725109sw (w : Nat) : Bool :=
  andB (subKOK (wC w) (wC w)) (andB (subKOK (D.a0B.getD w []) (wC w))
    (andB (subKOK (D.a1B.getD w []) (wC w))
      (subKOK (List.zipWith mmulK (D.a0B.getD w []) (D.a1B.getD w [])) (wC w))))

@[expose] noncomputable def ch725109sk (k : Nat) : Bool :=
  andB (subKOK (D.k1B.getD k []) (D.zB.getD (D.k1zw.getD k (0, 0)).1 []))
    (andB (subKOK (D.k1B.getD k []) (wC (D.k1zw.getD k (0, 0)).2))
      (irrK D.x7p D.x7q (D.k1B.getD k []) (wC (D.k1zw.getD k (0, 0)).2) (DI.irr1.getD k [])))

@[expose] noncomputable def ch725109sc (k : Nat) : Bool :=
  andB (subKOK (D.k2B.getD k []) (wC (D.k2w.getD k 0)))
    (irrK D.x7p D.x7q (D.k2B.getD k []) (wC (D.k2w.getD k 0)) (DI.irr2.getD k []))

#kc_each ch725109sz 0 7
#kc_each ch725109sw 0 2
#kc_each ch725109sk 0 6
#kc_each ch725109sc 0 12

theorem ch725109n_ebas :
    notB (ebasK (List.cons (D.zB.getD 0 [] |>.getD 0 0) (D.zB.getD 0 []))) = true := by
  quickRfl

theorem ch725109n_sub : notB (subKOK (D.k2B.getD 0 []) (D.zB.getD 0 [])) = true := by
  quickRfl

theorem ch725109n_irr : notB (irrK D.x7p D.x7q (D.k2B.getD 0 []) (wC (D.k2w.getD 0 0))
    (DI.irr2.getD 1 [])) = true := by
  quickRfl

end CertificateChecks.KernelL52I

end

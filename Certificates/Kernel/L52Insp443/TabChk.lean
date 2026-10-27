module

public import Certificates.Kernel.L52Insp443.Data
public import Certificates.Data.Kernel.L52Insp443.Tab
public import Certificates.Data.L52Insp443
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th.Native

@[expose] def k1idx (k : Nat) : Nat := [1, 2, 3, 4, 7, 8].getD k 0

@[expose] noncomputable def ch725109t (z : Nat) : Bool :=
  tabsK (D.zB.getD z []) (e16.getD z [])

@[expose] noncomputable def ch725109u (w : Nat) : Bool :=
  andB (tabsK (D.a0B.getD w []) (e64a0.getD w [])) (tabsK (D.a1B.getD w []) (e64a1.getD w []))

@[expose] noncomputable def ch725109q (k : Nat) : Bool :=
  tabsK (D.k1B.getD k []) (cands7.getD (k1idx k) [])

@[expose] noncomputable def ch725109r (k : Nat) : Bool :=
  tabsK (D.k2B.getD k []) (cands7.getD (k + 12) [])

@[expose] noncomputable def ch725109y (_ : Nat) : Bool :=
  andB (unitK (D.x7p.getD 1 0)) (tabK (D.x7p.getD 1 0) x7T)

#kc_each ch725109t 0 7
#kc_each ch725109u 0 2
#kc_each ch725109q 0 6
#kc_each ch725109r 0 12
#kc_each ch725109y 0 1

theorem ch725109n_tabs : notB (tabsK (D.zB.getD 1 []) (e16.getD 0 [])) = true := by
  quickRfl

theorem ch725109n_tab : notB (tabK (D.x7p.getD 2 0) x7T) = true := by
  quickRfl

theorem ch725109n_unit : notB (unitK (nat_lit 0)) = true := by
  quickRfl

theorem ch725109n_len : notB (tabsK (D.a0B.getD 0 []) (e16.getD 0 [])) = true := by
  quickRfl

end CertificateChecks.KernelL52I

end

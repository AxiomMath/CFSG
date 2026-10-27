module

public import Certificates.Kernel.Sporadic.Co1Row26683.Data
public import Certificates.Kernel.Co1B.TriD2045
public import Certificates.Data.Kernel.Spor.Co1Row26683K
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBCData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.KS.Co1Row26683 CertificateChecks.KernelCo1B.Tri2045 CertificateChecks.KernelSpor

@[expose] noncomputable def G (j : Nat) : Nat := nthN C26683.GK j

@[expose] noncomputable def ch26683G (k : Nat) : Bool :=
  withXY TB.P TB.PI (nat_lit 10) (nat_lit 11) fun X Y Xi Yi =>
    genSl X Y Xi Yi G C26683.WS (Nat.shiftRight k (nat_lit 2)) (Nat.land k (nat_lit 3))

end CertificateChecks.KernelSpor.Co1Row26683

#kc_each CertificateChecks.KernelSpor.Co1Row26683.ch26683G 0 16

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.KS.Co1Row26683 CertificateChecks.KernelCo1B.Tri2045 CertificateChecks.KernelSpor
  CFSG.EvenSporadicStandard.Solomon78

theorem ch26683B :
    baseK G C26683.RP C26683.QP C26683.QIP C26683.NC C26683.NCW C26683.ZQ = true := by
  quickRfl

theorem ch26683W :
    bAnd(eqWLI co1WordsS C26683.WS, eqWLI co1WordsC C26683.WC) = true := by
  quickRfl

theorem ch26683T1 :
    withXY TB.P TB.PI (nat_lit 10) (nat_lit 11)
      (fun X Y Xi Yi => tree1K X Y Xi Yi C26683.H1 C26683.T1R) = true := by
  quickRfl

theorem ch26683T2 :
    withXY TB.P TB.PI (nat_lit 10) (nat_lit 11) (fun X Y Xi Yi =>
      CFSG.KC.Enum.strictB (TB.P (nat_lit 5)) fun F =>
        tree2K X Y Xi Yi F C26683.H2 C26683.T2R C26683.U0 C26683.U1 C26683.A2) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Co1Row26683

end

module

public import Certificates.Data.Kernel.E6TT.Row
public import Certificates.Kernel.E6TT.Data
public import Certificates.Kernel.E6TT.WeylData
public import Certificates.Kernel.E6TT.RowData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE6TT

open CFSG.KC.E6TT Certificates.Data.E6TableT

theorem rootsV : (vecs RV.V 72 == roots ()) = true := by quickRfl

theorem hsA2 : hsK W.H0 = true := by quickRfl

theorem hsA4A1 : hsK W.H1 = true := by quickRfl

theorem hsD4 : hsK W.H2 = true := by quickRfl

theorem hsA5 : hsK W.H3 = true := by quickRfl

theorem hsD5 : hsK W.H4 = true := by quickRfl

theorem mapsA4A1 :
    Nat.beq (enumK D.GR D.L1 D.N11 D.N12 D.N13 D.N14 D.N15 (leafK 1 W.H1 W.O1 RV.V)) 0 = true := by
  quickRfl

theorem mapsD4 :
    Nat.beq (enumK D.GR D.L2 D.N21 D.N22 D.N23 D.N24 D.N25 (leafK 2 W.H2 W.O2 RV.V)) 0 = true := by
  quickRfl

theorem mapsA5 :
    Nat.beq (enumK D.GR D.L3 D.N31 D.N32 D.N33 D.N34 D.N35 (leafK 3 W.H3 W.O3 RV.V)) 0 = true := by
  quickRfl

theorem mapsD5 :
    Nat.beq (enumK D.GR D.L4 D.N41 D.N42 D.N43 D.N44 D.N45 (leafK 4 W.H4 W.O4 RV.V)) 0 = true := by
  quickRfl

end CertificateChecks.KernelE6TT

end

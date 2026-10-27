module

public import Certificates.Kernel.Co1B.Chk2047
public import Certificates.Data.Kernel.Co1PW
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import Certificates.Kernel.LocalComp.Co1Cen2CIn
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo1Cen2CData

public section

set_option maxRecDepth 400000

#kss_co1dag CertificateChecks.KernelLC.Co1Cen2C.G CertificateChecks.KernelLC.Co1Cen2C.globDag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2C.P1 CertificateChecks.KernelLC.Co1Cen2C.pw1Dag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2C.P2 CertificateChecks.KernelLC.Co1Cen2C.pw2Dag
#kss_co1dag CertificateChecks.KernelLC.Co1Cen2C.R CertificateChecks.KernelLC.Co1Cen2C.rDag

namespace CertificateChecks.KernelLC.Co1Cen2C

open CFSG.KC.Enum CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KD.Co1B CFSG.KC.Co1PW
open CFSG.ComponentClassification.RankTwoSporadic.Co1
open CertificateChecks.KernelCo1B.C2047 (IC QM RK)
open CFSG.KC.Co1B (mulWK)

@[expose] noncomputable def SK : List Nat := [G.M 222, G.M 223, G.M 231, G.M 226, G.M 228]

theorem kG0 : (Nat.beq (G.M 0) SA && Nat.beq (G.M 1) SB && Nat.beq (G.M 2) IC &&
    allN 11 (fun l => Nat.beq (G.M (3 + l)) (QM l))) = true := by quickRfl

theorem kG : dagK G.M G.MI 14 G.N co1Cen2CGlobal = true := by quickRfl

theorem kS : ((co1Cen2CS1 ++ co1Cen2CS2).all (okK G.N)) = true := by quickRfl

theorem kP1 : (Nat.beq (P1.M 0) (G.M 222) && Nat.beq (P1.M 1) (G.M 223) &&
    Nat.beq (P1.M 2) (G.M 231)) = true := by quickRfl

theorem kP2 : (Nat.beq (P2.M 0) (G.M 226) && Nat.beq (P2.M 1) (G.M 228)) = true := by quickRfl

theorem kD1 : dagK P1.M P1.MI 3 P1.N co1Cen2CD1 = true := by quickRfl

theorem kD2 : dagK P2.M P2.MI 2 P2.N co1Cen2CD2 = true := by quickRfl

theorem kW1 : pwCoreK P1.M P1.MI P1.N [G.M 222, G.M 223, G.M 231] co1Cen2CZH1.1 co1Cen2CZH1.2
    co1Cen2CDec1 IC = true := by quickRfl

theorem kW2 : pwCoreK P2.M P2.MI P2.N [G.M 226, G.M 228] co1Cen2CZH2.1 co1Cen2CZH2.2
    co1Cen2CDec2 IC = true := by quickRfl

theorem kR0 : allN 5 (fun i => Nat.beq (R.M i) (SK.getD i 0)) = true := by quickRfl

theorem kR : dagK R.M R.MI 5 R.N co1Cen2CRD = true := by quickRfl

theorem kRe : (co1Cen2CRE.all (okK R.N) && Nat.beq (R.M 5) (RK 0) && Nat.beq (R.M 6) (RK 1) &&
    Nat.beq (R.M 7) (RK 2)) = true := by quickRfl

@[expose] noncomputable def scanPt (X : Nat) : Bool :=
  unpack 24 24 X == unpack 24 24 idM || unpack 24 24 X == unpack 24 24 IC ||
    SK.any fun s => !(unpack 24 24 (mulWK X s) == unpack 24 24 (mulWK s X))

theorem kScan : allN 2048 (fun i => scanPt (CertificateChecks.KernelCo1B.C2047.QT.P i)) = true := by
  quickRfl

end CertificateChecks.KernelLC.Co1Cen2C

end

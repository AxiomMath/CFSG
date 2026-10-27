module

public import Certificates.Kernel.J4M2.C12607Checks
public import Certificates.Data.Kernel.SporSch.J4SBig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4JSData
public meta import Certificates.Kernel.SporSch.J4S.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_rows CertificateChecks.KernelJ4JS.PJ CFSG.Sporadic.J4Schreier.jsJP
#kss_rows CertificateChecks.KernelJ4JS.IJ CFSG.Sporadic.J4Schreier.jsJPinv
#kss_rows CertificateChecks.KernelJ4JS.RJ CFSG.Sporadic.J4Schreier.jsJR
#kss_rows CertificateChecks.KernelJ4JS.PS CFSG.Sporadic.J4Schreier.jsSP
#kss_rows CertificateChecks.KernelJ4JS.IS CFSG.Sporadic.J4Schreier.jsSPinv
#kss_rows CertificateChecks.KernelJ4JS.RS CFSG.Sporadic.J4Schreier.jsSR

namespace CertificateChecks.KernelJ4JS

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier
  CertificateChecks.KernelSporSch.J4E7 CertificateChecks.KernelJ4Gam

@[expose] noncomputable def SP : Nat × Nat := pP (mP (pP H1 2) (pP H2 5)) 11

@[expose] noncomputable def QP : Nat × Nat := mP (pP (V 3) 8) (pP (V 4) 4)

theorem pj : packNK jsJP.toList PJ = true := by quickRfl
theorem ij : packNK jsJPinv.toList IJ = true := by quickRfl
theorem rj : packNK jsJR.toList RJ = true := by quickRfl
theorem ps : packNK jsSP.toList PS = true := by quickRfl
theorem iS : packNK jsSPinv.toList IS = true := by quickRfl
theorem rs : packNK jsSR.toList RS = true := by quickRfl

theorem fj : CFSG.KS.SporSch.J4E.fixK c rm one JP.1 PJ IJ RJ 62 = true := by quickRfl
theorem fs : CFSG.KS.SporSch.J4E.fixK c rm one SP.1 PS IS RS 56 = true := by quickRfl

theorem nfj : notB (CFSG.KS.SporSch.J4E.fixK c rm one JP.1 PJ IJ RJ 61) = true := by quickRfl
theorem nfs : notB (CFSG.KS.SporSch.J4E.fixK c rm one SP.1 PS IS RS 57) = true := by quickRfl

theorem jj : Nat.beq (mulJ c rm JP.1 JP.1) one = true := by quickRfl
theorem ss : Nat.beq (mulJ c rm SP.1 SP.1) one = true := by quickRfl
theorem sq : Nat.beq (mulJ c rm SP.1 QP.1) (mulJ c rm QP.1 SP.1) = true := by quickRfl

theorem nsq : notB (Nat.beq (mulJ c rm SP.1 QP.1) QP.1) = true := by quickRfl

end CertificateChecks.KernelJ4JS

end

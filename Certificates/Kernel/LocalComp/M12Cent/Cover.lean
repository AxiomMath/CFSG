module

public import Certificates.Kernel.LocalComp.M12Cent.Data
public meta import Certificates.Kernel.LocalComp.M12Cent.Data
public import Certificates.Data.E3S3GenM12
public meta import Certificates.Data.E3S3GenM12
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.M12Cent

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.Schreier CFSG.ComponentClassification.M12Cover
open CFSG.ClassicalInvolution.Q3.TL4.E3S3M12

meta def RB1 : List (Array Nat) :=
  evalW 12 #[tA, tB] (m12InvRepWords.getD 0 []) :: gen1Data.map fun d => evalW 12 G1 d.sw

meta def RB3 : List (Array Nat) :=
  evalW 12 #[tA, tB] (m12InvRepWords.getD 1 []) :: gen2Data.map fun d => evalW 12 G3 d.sw

end CertificateChecks.KernelLC.M12Cent

end

#kss_cntord CertificateChecks.KernelLC.M12Cent.Y1 CertificateChecks.KernelLC.M12Cent.C1 12 4
  CertificateChecks.KernelLC.M12Cent.S1 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One12 CertificateChecks.KernelLC.M12Cent.id12 2

#kss_cntord CertificateChecks.KernelLC.M12Cent.Y3 CertificateChecks.KernelLC.M12Cent.C3 12 4
  CertificateChecks.KernelLC.M12Cent.S3 CertificateChecks.KernelLC.M12Cent.base3
  CertificateChecks.KernelLC.M12Cent.One12 CertificateChecks.KernelLC.M12Cent.id12 2

#lc_reps CertificateChecks.KernelLC.M12Cent.T1 4 CertificateChecks.KernelLC.M12Cent.G1
  CertificateChecks.KernelLC.M12Cent.RB1

#lc_reps CertificateChecks.KernelLC.M12Cent.T3 4 CertificateChecks.KernelLC.M12Cent.G3
  CertificateChecks.KernelLC.M12Cent.RB3

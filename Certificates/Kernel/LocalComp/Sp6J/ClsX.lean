module

public import Certificates.Kernel.LocalComp.Sp6J.Data
public import Certificates.Kernel.LocalComp.Child3Gen
public meta import Certificates.Kernel.LocalComp.Sp6J.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Sp6J

open CFSG.KS.SporSch.MOCG CFSG.EvenSmallLie.Sp6

meta def RXL : List (Array Nat) := sp6InvRepWords.map (evalW 36 XG)

end CertificateChecks.KernelLC.Sp6J

#lc_reps CertificateChecks.KernelLC.Sp6J.RX 6 CertificateChecks.KernelLC.Sp6J.XG
  CertificateChecks.KernelLC.Sp6J.RXL

end

module

public import Certificates.Kernel.LocalComp.Sp6J.Data
public import Certificates.Kernel.LocalComp.Child3Gen
public meta import Certificates.Kernel.LocalComp.Sp6J.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelLC.Sp6J

open CFSG.KS.SporSch.MOCG

meta def RF1L : List (Array Nat) := f1Words.map (evalW 36 CG1)

meta def RF2L : List (Array Nat) := f2Words.map (evalW 36 CG2)

meta def RF3L : List (Array Nat) := f3Words.map (evalW 36 CG3)

meta def RF4L : List (Array Nat) := f4Words.map (evalW 36 CG4)

end CertificateChecks.KernelLC.Sp6J

#lc_reps CertificateChecks.KernelLC.Sp6J.RF1 6 CertificateChecks.KernelLC.Sp6J.CG1
  CertificateChecks.KernelLC.Sp6J.RF1L

#lc_reps CertificateChecks.KernelLC.Sp6J.RF2 6 CertificateChecks.KernelLC.Sp6J.CG2
  CertificateChecks.KernelLC.Sp6J.RF2L

#lc_reps CertificateChecks.KernelLC.Sp6J.RF3 6 CertificateChecks.KernelLC.Sp6J.CG3
  CertificateChecks.KernelLC.Sp6J.RF3L

#lc_reps CertificateChecks.KernelLC.Sp6J.RF4 6 CertificateChecks.KernelLC.Sp6J.CG4
  CertificateChecks.KernelLC.Sp6J.RF4L

end

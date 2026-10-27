module

public import Certificates.Kernel.SporSch.Mathieu.M11Data
public import Certificates.Kernel.LocalComp.Child3Gen
public meta import Certificates.Kernel.SporSch.Mathieu.M11Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11H1

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M11OC

meta def G4 : Array (Array Nat) := SC1.extract 0 4

meta def fourW : List (List Int) := [[1, 3]]

meta def RA : List (Array Nat) := fourW.map (evalW 11 G4)

end CertificateChecks.KernelSporSch.M11H1

#kss_cntord CertificateChecks.KernelSporSch.M11H1X CertificateChecks.KernelSporSch.M11C1 11 4
  CertificateChecks.KernelSporSch.M11OC.SC1 CertificateChecks.KernelSporSch.M11OC.baseC1
  CertificateChecks.KernelSporSch.M11OC.One CertificateChecks.KernelSporSch.M11OC.oneM 4

#lc_reps CertificateChecks.KernelSporSch.M11H1R 4 CertificateChecks.KernelSporSch.M11H1.G4
  CertificateChecks.KernelSporSch.M11H1.RA

end

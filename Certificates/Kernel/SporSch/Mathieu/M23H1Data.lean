module

public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Kernel.LocalComp.Child3Gen
public meta import Certificates.Kernel.SporSch.Mathieu.M23Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23H1

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M23OC

@[expose] noncomputable def One23 : Nat := CFSG.KC.Enum.pidn 23 5

meta def id23 : Array Nat := idA 23

meta def G4 : Array (Array Nat) := SC1.extract 0 4

meta def fourW : List (List Int) :=
  [[-2, 4, -3, -1, -2, 4, -2, 4, 3, 3], [-1, 4, 3, 3, 4, 1, -4, 3, 4, 1], [4, 3, 3, 4, 4, 2]]

meta def RA : List (Array Nat) := fourW.map (evalW 23 G4)

end CertificateChecks.KernelSporSch.M23H1

#kss_cntord CertificateChecks.KernelSporSch.M23H1X CertificateChecks.KernelSporSch.M23C1 23 5
  CertificateChecks.KernelSporSch.M23OC.SC1 CertificateChecks.KernelSporSch.M23OC.baseC
  CertificateChecks.KernelSporSch.M23H1.One23 CertificateChecks.KernelSporSch.M23H1.id23 4

#lc_reps CertificateChecks.KernelSporSch.M23H1R 5 CertificateChecks.KernelSporSch.M23H1.G4
  CertificateChecks.KernelSporSch.M23H1.RA

end

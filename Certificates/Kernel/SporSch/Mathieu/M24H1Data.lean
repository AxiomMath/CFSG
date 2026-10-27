module

public import Certificates.Kernel.SporSch.Mathieu.M24Data
public import Certificates.Kernel.LocalComp.Child3Gen
public meta import Certificates.Kernel.SporSch.Mathieu.M24Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M24H1

open CFSG.KS.SporSch.MOCG CertificateChecks.KernelSporSch.M24OC

@[expose] noncomputable def One24 : Nat := CFSG.KC.Enum.pidn 24 5

meta def id24 : Array Nat := idA 24

meta def G1 : Array (Array Nat) := SC1.extract 0 3

meta def G2 : Array (Array Nat) := SC2.extract 0 2

meta def fourW1 : List (List Int) :=
  [[-3, -2, -2, -3, -1, 2, -1, 2, 3, 3, 1], [1, -2, -3, -2, 1, 2, 3, 1],
   [-3, -2, 3, -1, -1, -1, -1, 2, 3, 3, 1], [-2, -3, 1, 1, 3, -2, -1, 2, 1, 1],
   [1, 2, 3, -2, 1, -2, 1, 1], [-3, -2, -1, 2, -1, -3, -1, -1, -2, -3, 2],
   [2, -3, -2, -1, -1, -1, 2], [3, -2, -1, 2, 2], [-1, -3, -2, -3, -1, -2, -2, -3, 2, 2]]

meta def fourW2 : List (List Int) :=
  [[-1, -1, -1, -2, -2, 1, -2, -1, 2, 1, 1, -2, -2, 1, -2],
   [2, -1, 2, 2, 1, -2, 1, 1, -2, -1, -2, -1, 2, 1, 2, 1, 1, 1, 2, 1, 1],
   [1, 2, -1, -1, 2, 2, 1, 1, -2, -1, 2, -1, -1, -1, 2, -1, -2, 1, -2],
   [-1, 2, 2, 1, 1, 1, 2, -1, -1, 2, 1, 1, 2, -1, 2],
   [-1, -1, -1, -2, -2, 1, -2, 1, -2, -2, -1, 2, 2, -1, -2, -2, 1, -2],
   [-1, -1, -2, -1, -2, -2, -1, -2, 1, 2, 2, -1, 2, -1, -2, -1, -2, -2, 1, 2],
   [-2, -1, 2, 1, 1, 1, -2, -2, 1, 1, 1], [1, 1, 1, 2, -1, 2, 2, 1, -2, -1, -2, -1, -2, -2, 1, 2],
   [1, 1, -2, -1, -1, 2, -1, 2, -1, -2, -1, -2, -1, -1, -1, 2, 1, 1, 2, -1, 2],
   [-2, 1, 2, 1, 1, -2, -1, -2, -2, -2, -1, -1, -1, -2, -2, -2, 1, 2, 2, -1, 2, 2, 1],
   [-2, -1, -2, -2, -2, -1, -1, -1, -2, 1, 2, -1, -2, -2, 1, -2]]

meta def RA1 : List (Array Nat) := fourW1.map (evalW 24 G1)

meta def RA2 : List (Array Nat) := fourW2.map (evalW 24 G2)

end CertificateChecks.KernelSporSch.M24H1

#kss_cntord CertificateChecks.KernelSporSch.M24H1X1 CertificateChecks.KernelSporSch.M24C1 24 5
  CertificateChecks.KernelSporSch.M24OC.SC1 CertificateChecks.KernelSporSch.M24OC.baseC1
  CertificateChecks.KernelSporSch.M24H1.One24 CertificateChecks.KernelSporSch.M24H1.id24 4

#kss_cntord CertificateChecks.KernelSporSch.M24H1X2 CertificateChecks.KernelSporSch.M24C2 24 5
  CertificateChecks.KernelSporSch.M24OC.SC2 CertificateChecks.KernelSporSch.M24OC.baseC2
  CertificateChecks.KernelSporSch.M24H1.One24 CertificateChecks.KernelSporSch.M24H1.id24 4

#lc_reps CertificateChecks.KernelSporSch.M24H1R1 5 CertificateChecks.KernelSporSch.M24H1.G1
  CertificateChecks.KernelSporSch.M24H1.RA1

#lc_reps CertificateChecks.KernelSporSch.M24H1R2 5 CertificateChecks.KernelSporSch.M24H1.G2
  CertificateChecks.KernelSporSch.M24H1.RA2

end

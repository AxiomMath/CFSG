
module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM24Data
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.M24Base
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M24OC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m24gA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m24gB).toArray

meta def SM : Array (Array Nat) := strongOf 24 #[tAM, tBM] CFSG.Sporadic.Schreier.m24Words

meta def baseM : Array Nat := #[0, 1, 2, 3, 4, 5, 6]

meta def SC1 : Array (Array Nat) :=
  strongOf 24 (CFSG.Sporadic.Schreier.m24CentWords1.map (evalW 24 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m24CentChainWords1

meta def baseC1 : Array Nat := #[0, 1, 2]

meta def SC2 : Array (Array Nat) :=
  strongOf 24 (CFSG.Sporadic.Schreier.m24CentWords2.map (evalW 24 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m24CentChainWords2

meta def baseC2 : Array Nat := #[1, 0, 2, 3]

meta def repsM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m24InvRepWords.map (evalW 24 #[tAM, tBM])).toArray

@[expose] def pairWs : List (List Nat × Nat) := [([0, 1], 23), ([0, 1, 2, 3], 12)]

end CertificateChecks.KernelSporSch.M24OC

#kss_list CertificateChecks.KernelSporSch.M24OC.tA CertificateChecks.KernelSporSch.M24OC.tAM

#kss_list CertificateChecks.KernelSporSch.M24OC.tB CertificateChecks.KernelSporSch.M24OC.tBM

#ks_rawchain CertificateChecks.KernelSporSch.M24Q 24 5 16 CertificateChecks.KernelSporSch.M24OC.SM
  CertificateChecks.KernelSporSch.M24OC.baseM 2 CFSG.Sporadic.Schreier.m24Words

#ks_rawchain CertificateChecks.KernelSporSch.M24C1 24 5 16 CertificateChecks.KernelSporSch.M24OC.SC1
  CertificateChecks.KernelSporSch.M24OC.baseC1 3 CFSG.Sporadic.Schreier.m24CentChainWords1

#ks_rawchain CertificateChecks.KernelSporSch.M24C2 24 5 16 CertificateChecks.KernelSporSch.M24OC.SC2
  CertificateChecks.KernelSporSch.M24OC.baseC2 2 CFSG.Sporadic.Schreier.m24CentChainWords2

end


module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Mathieu.Simple
public import CFSG.Sporadic.Schreier.M23Base
public meta import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M23CheckBase
public meta import CFSG.Sporadic.Schreier.M23CheckBase
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.Outer
public meta import CFSG.Sporadic.Schreier.Outer

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23OC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m23PermA).toArray

meta def tBM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m23PermB).toArray

meta def SM : Array (Array Nat) := strongOf 23 #[tAM, tBM] CFSG.Sporadic.Schreier.m23Words

meta def baseM : Array Nat := #[0, 1, 2, 3, 4, 5]

meta def SC1 : Array (Array Nat) :=
  strongOf 23 (CFSG.Sporadic.Schreier.m23CentWords1.map (evalW 23 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m23CentChainWords1

meta def baseC : Array Nat := #[2, 0, 5, 4]

meta def repsM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m23InvRepWords.map (evalW 23 #[tAM, tBM])).toArray

@[expose] def pairWs : List (List Nat × Nat) := [([0, 1], 23), ([0, 1, 2, 3], 6)]

end CertificateChecks.KernelSporSch.M23OC

#kss_list CertificateChecks.KernelSporSch.M23OC.tA CertificateChecks.KernelSporSch.M23OC.tAM

#kss_list CertificateChecks.KernelSporSch.M23OC.tB CertificateChecks.KernelSporSch.M23OC.tBM

#ks_rawchain CertificateChecks.KernelSporSch.M23Q 23 5 16 CertificateChecks.KernelSporSch.M23OC.SM
  CertificateChecks.KernelSporSch.M23OC.baseM 2 CFSG.Sporadic.Schreier.m23Words

#ks_rawchain CertificateChecks.KernelSporSch.M23C1 23 5 16 CertificateChecks.KernelSporSch.M23OC.SC1
  CertificateChecks.KernelSporSch.M23OC.baseC 4 CFSG.Sporadic.Schreier.m23CentChainWords1

#kss_odd CertificateChecks.KernelSporSch.M23O1 CertificateChecks.KernelSporSch.M23C1 23 5
  CertificateChecks.KernelSporSch.M23OC.SC1 CertificateChecks.KernelSporSch.M23OC.baseC 21

end

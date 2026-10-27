module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22Data
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22OC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m22gA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m22gB).toArray

meta def SM : Array (Array Nat) := strongOf 22 #[tAM, tBM] CFSG.Sporadic.Schreier.m22Words

meta def baseM : Array Nat := #[0, 1, 2, 3, 4]

meta def SC1 : Array (Array Nat) :=
  strongOf 22 (CFSG.Sporadic.Schreier.m22CentWords1.map (evalW 22 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m22CentChainWords1

meta def baseC : Array Nat := #[0, 1, 2]

meta def repsM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m22InvRepWords.map (evalW 22 #[tAM, tBM])).toArray

meta def rep0M : Array Nat := repsM[0]!

meta def oneM : Array Nat := idA 22

end CertificateChecks.KernelSporSch.M22OC

#kss_list CertificateChecks.KernelSporSch.M22OC.tA CertificateChecks.KernelSporSch.M22OC.tAM

#kss_list CertificateChecks.KernelSporSch.M22OC.tB CertificateChecks.KernelSporSch.M22OC.tBM

#ks_rawchain CertificateChecks.KernelSporSch.M22Q 22 5 16 CertificateChecks.KernelSporSch.M22OC.SM
  CertificateChecks.KernelSporSch.M22OC.baseM 2 CFSG.Sporadic.Schreier.m22Words

#ks_rawchain CertificateChecks.KernelSporSch.M22C1 22 5 16 CertificateChecks.KernelSporSch.M22OC.SC1
  CertificateChecks.KernelSporSch.M22OC.baseC 3 CFSG.Sporadic.Schreier.m22CentChainWords1

#kss_classes CertificateChecks.KernelSporSch.M22CL 22 5 CertificateChecks.KernelSporSch.M22OC.tAM
  CertificateChecks.KernelSporSch.M22OC.tBM CertificateChecks.KernelSporSch.M22OC.repsM

namespace CertificateChecks.KernelSporSch.M22OC

@[expose] noncomputable def One : Nat := CFSG.KC.Enum.pidn 22 5

@[expose] noncomputable def R0 : Nat := (M22CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1

end CertificateChecks.KernelSporSch.M22OC

#kss_odd CertificateChecks.KernelSporSch.M22O1 CertificateChecks.KernelSporSch.M22C1 22 5
  CertificateChecks.KernelSporSch.M22OC.SC1 CertificateChecks.KernelSporSch.M22OC.baseC 3

end

module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM11Data
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M11OC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m11gA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m11gB).toArray

meta def SM : Array (Array Nat) := strongOf 11 #[tAM, tBM] CFSG.Sporadic.Schreier.m11Words

meta def baseM : Array Nat := #[0, 1, 2, 3]

meta def SC1 : Array (Array Nat) :=
  strongOf 11 (CFSG.Sporadic.Schreier.m11CentWords1.map (evalW 11 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m11CentChainWords1

meta def baseC1 : Array Nat := #[0, 1, 2]

meta def repsM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m11InvRepWords.map (evalW 11 #[tAM, tBM])).toArray

meta def rep0M : Array Nat := repsM[0]!

meta def oneM : Array Nat := idA 11

end CertificateChecks.KernelSporSch.M11OC

#kss_list CertificateChecks.KernelSporSch.M11OC.tA CertificateChecks.KernelSporSch.M11OC.tAM

#kss_list CertificateChecks.KernelSporSch.M11OC.tB CertificateChecks.KernelSporSch.M11OC.tBM

#ks_rawchain CertificateChecks.KernelSporSch.M11Q 11 4 16 CertificateChecks.KernelSporSch.M11OC.SM
  CertificateChecks.KernelSporSch.M11OC.baseM 2 CFSG.Sporadic.Schreier.m11Words

#ks_rawchain CertificateChecks.KernelSporSch.M11C1 11 4 16 CertificateChecks.KernelSporSch.M11OC.SC1
  CertificateChecks.KernelSporSch.M11OC.baseC1 4 CFSG.Sporadic.Schreier.m11CentChainWords1

#kss_classes CertificateChecks.KernelSporSch.M11CL 11 4 CertificateChecks.KernelSporSch.M11OC.tAM
  CertificateChecks.KernelSporSch.M11OC.tBM CertificateChecks.KernelSporSch.M11OC.repsM

namespace CertificateChecks.KernelSporSch.M11OC

@[expose] noncomputable def One : Nat := CFSG.KC.Enum.pidn 11 4

@[expose] noncomputable def R0 : Nat := (M11CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1

end CertificateChecks.KernelSporSch.M11OC

#kss_cntord CertificateChecks.KernelSporSch.M11X CertificateChecks.KernelSporSch.M11Q 11 4
  CertificateChecks.KernelSporSch.M11OC.SM CertificateChecks.KernelSporSch.M11OC.baseM
  CertificateChecks.KernelSporSch.M11OC.One CertificateChecks.KernelSporSch.M11OC.oneM 2

#kss_cntword CertificateChecks.KernelSporSch.M11Y CertificateChecks.KernelSporSch.M11Q 11 4
  CertificateChecks.KernelSporSch.M11OC.SM CertificateChecks.KernelSporSch.M11OC.baseM 2 4
  CFSG.Sporadic.Schreier.m11AutWords CertificateChecks.KernelSporSch.M11OC.R0
  CertificateChecks.KernelSporSch.M11OC.rep0M

#kss_odd CertificateChecks.KernelSporSch.M11O CertificateChecks.KernelSporSch.M11C1 11 4
  CertificateChecks.KernelSporSch.M11OC.SC1 CertificateChecks.KernelSporSch.M11OC.baseC1 3

end

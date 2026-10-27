module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.M12
public meta import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12OC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m12gA).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Mathieu.m12gB).toArray

meta def SM : Array (Array Nat) := strongOf 12 #[tAM, tBM] CFSG.Sporadic.Schreier.m12Words

meta def baseM : Array Nat := #[0, 1, 2, 3, 4]

meta def SC1 : Array (Array Nat) :=
  strongOf 12 (CFSG.Sporadic.Schreier.m12CentWords1.map (evalW 12 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m12CentChainWords1

meta def SC2 : Array (Array Nat) :=
  strongOf 12 (CFSG.Sporadic.Schreier.m12CentWords2.map (evalW 12 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m12CentChainWords2

meta def baseC : Array Nat := #[0, 1, 2]

meta def repsM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m12InvRepWords.map (evalW 12 #[tAM, tBM])).toArray

meta def rep0M : Array Nat := repsM[0]!

meta def rep1M : Array Nat := repsM[1]!

meta def oneM : Array Nat := idA 12

end CertificateChecks.KernelSporSch.M12OC

#kss_list CertificateChecks.KernelSporSch.M12OC.tA CertificateChecks.KernelSporSch.M12OC.tAM

#kss_list CertificateChecks.KernelSporSch.M12OC.tB CertificateChecks.KernelSporSch.M12OC.tBM

#ks_rawchain CertificateChecks.KernelSporSch.M12Q 12 4 16 CertificateChecks.KernelSporSch.M12OC.SM
  CertificateChecks.KernelSporSch.M12OC.baseM 2 CFSG.Sporadic.Schreier.m12Words

#ks_rawchain CertificateChecks.KernelSporSch.M12C1 12 4 16 CertificateChecks.KernelSporSch.M12OC.SC1
  CertificateChecks.KernelSporSch.M12OC.baseC 4 CFSG.Sporadic.Schreier.m12CentChainWords1

#ks_rawchain CertificateChecks.KernelSporSch.M12C2 12 4 16 CertificateChecks.KernelSporSch.M12OC.SC2
  CertificateChecks.KernelSporSch.M12OC.baseC 3 CFSG.Sporadic.Schreier.m12CentChainWords2

#kss_classes CertificateChecks.KernelSporSch.M12CL 12 4 CertificateChecks.KernelSporSch.M12OC.tAM
  CertificateChecks.KernelSporSch.M12OC.tBM CertificateChecks.KernelSporSch.M12OC.repsM

namespace CertificateChecks.KernelSporSch.M12OC

@[expose] noncomputable def One : Nat := CFSG.KC.Enum.pidn 12 4

@[expose] noncomputable def R0 : Nat := (M12CL.getD 0 (0, 0, 0, [], [], [], [])).2.2.1

@[expose] noncomputable def R1 : Nat := (M12CL.getD 1 (0, 0, 0, [], [], [], [])).2.2.1

end CertificateChecks.KernelSporSch.M12OC

#kss_cntord CertificateChecks.KernelSporSch.M12X CertificateChecks.KernelSporSch.M12Q 12 4
  CertificateChecks.KernelSporSch.M12OC.SM CertificateChecks.KernelSporSch.M12OC.baseM
  CertificateChecks.KernelSporSch.M12OC.One CertificateChecks.KernelSporSch.M12OC.oneM 2

#kss_cntword CertificateChecks.KernelSporSch.M12Y0 CertificateChecks.KernelSporSch.M12Q 12 4
  CertificateChecks.KernelSporSch.M12OC.SM CertificateChecks.KernelSporSch.M12OC.baseM 2 3
  CFSG.Sporadic.Schreier.m12AutWords CertificateChecks.KernelSporSch.M12OC.R0
  CertificateChecks.KernelSporSch.M12OC.rep0M

#kss_cntword CertificateChecks.KernelSporSch.M12Y1 CertificateChecks.KernelSporSch.M12Q 12 4
  CertificateChecks.KernelSporSch.M12OC.SM CertificateChecks.KernelSporSch.M12OC.baseM 2 3
  CFSG.Sporadic.Schreier.m12AutWords CertificateChecks.KernelSporSch.M12OC.R1
  CertificateChecks.KernelSporSch.M12OC.rep1M

#kss_odd CertificateChecks.KernelSporSch.M12O1 CertificateChecks.KernelSporSch.M12C1 12 4
  CertificateChecks.KernelSporSch.M12OC.SC1 CertificateChecks.KernelSporSch.M12OC.baseC 3

#kss_odd CertificateChecks.KernelSporSch.M12O2 CertificateChecks.KernelSporSch.M12C2 12 4
  CertificateChecks.KernelSporSch.M12OC.SC2 CertificateChecks.KernelSporSch.M12OC.baseC 15

end

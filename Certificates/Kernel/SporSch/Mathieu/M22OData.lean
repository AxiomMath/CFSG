module

public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Kernel.SporSch.Mathieu.Gen2
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
public meta import Certificates.Kernel.SporSch.Mathieu.M22Data
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22OuterData
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M22OC

open CFSG.KS.SporSch.MOCG

meta def tDM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m22Delta).toArray

meta def SO1 : Array (Array Nat) :=
  strongOf 22 (CFSG.Sporadic.Schreier.m22OutCentWords1.map (evalW 22 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m22OutCentChainWords1

meta def SO2 : Array (Array Nat) :=
  strongOf 22 (CFSG.Sporadic.Schreier.m22OutCentWords2.map (evalW 22 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m22OutCentChainWords2

meta def orepsM : Array (Array Nat) :=
  (CFSG.Sporadic.Schreier.m22OutRepWords.map fun wd => comp (evalW 22 #[tAM, tBM] wd) tDM).toArray

end CertificateChecks.KernelSporSch.M22OC

#kss_list CertificateChecks.KernelSporSch.M22OC.tD CertificateChecks.KernelSporSch.M22OC.tDM

#ks_perm CertificateChecks.KernelSporSch.M22D 5 CertificateChecks.KernelSporSch.M22OC.tDM

#ks_rawchain CertificateChecks.KernelSporSch.M22OC1 22 5 16 CertificateChecks.KernelSporSch.M22OC.SO1
  CertificateChecks.KernelSporSch.M22OC.baseC 3 CFSG.Sporadic.Schreier.m22OutCentChainWords1

#ks_rawchain CertificateChecks.KernelSporSch.M22OC2 22 5 16 CertificateChecks.KernelSporSch.M22OC.SO2
  CertificateChecks.KernelSporSch.M22OC.baseC 3 CFSG.Sporadic.Schreier.m22OutCentChainWords2

#kss_classes2 CertificateChecks.KernelSporSch.M22OCL 22 5 CertificateChecks.KernelSporSch.M22OC.tAM
  CertificateChecks.KernelSporSch.M22OC.tBM CertificateChecks.KernelSporSch.M22OC.tA
  CertificateChecks.KernelSporSch.M22OC.tB CertificateChecks.KernelSporSch.M22OC.orepsM 2 2000

namespace CertificateChecks.KernelSporSch.M22OC

@[expose] noncomputable def RO0 : Nat := (M22OCL.getD 0 CFSG.KS.SporSch.MOC.clsD0).R

@[expose] noncomputable def RO1 : Nat := (M22OCL.getD 1 CFSG.KS.SporSch.MOC.clsD0).R

@[expose] noncomputable def A0 : Nat := M22Q.S 0

@[expose] noncomputable def B0 : Nat := M22Q.S 1

end CertificateChecks.KernelSporSch.M22OC

#kss_odd CertificateChecks.KernelSporSch.M22OO1 CertificateChecks.KernelSporSch.M22OC1 22 5
  CertificateChecks.KernelSporSch.M22OC.SO1 CertificateChecks.KernelSporSch.M22OC.baseC 5

#kss_odd CertificateChecks.KernelSporSch.M22OO2 CertificateChecks.KernelSporSch.M22OC2 22 5
  CertificateChecks.KernelSporSch.M22OC.SO2 CertificateChecks.KernelSporSch.M22OC.baseC 21

end

module

public import Certificates.Kernel.SporSch.Mathieu.Gen2
public import Certificates.Kernel.SporSch.Mathieu.Gen3
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12ModelData
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import CFSG.Sporadic.Schreier.MathieuOddCoreOuter
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreOuter

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M12MOC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m12A1).toArray

meta def tBM : Array Nat := (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m12B1).toArray

meta def tSM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList CFSG.Sporadic.Schreier.m12Sigma).toArray

meta def SM : Array (Array Nat) := strongOf 24 #[tAM, tBM] CFSG.Sporadic.Schreier.m12Words

meta def baseM : Array Nat := #[0, 1, 2, 3, 4]

meta def SC : Array (Array Nat) :=
  strongOf 24 (CFSG.Sporadic.Schreier.m12SigmaCentWords.map (evalW 24 #[tAM, tBM])).toArray
    CFSG.Sporadic.Schreier.m12SigmaCentChainWords

meta def baseC : Array Nat := #[1, 0, 2]

meta def repsM : Array (Array Nat) := #[tSM]

end CertificateChecks.KernelSporSch.M12MOC

#kss_list CertificateChecks.KernelSporSch.M12MOC.tA CertificateChecks.KernelSporSch.M12MOC.tAM

#kss_list CertificateChecks.KernelSporSch.M12MOC.tB CertificateChecks.KernelSporSch.M12MOC.tBM

#kss_list CertificateChecks.KernelSporSch.M12MOC.tS CertificateChecks.KernelSporSch.M12MOC.tSM

#ks_perm CertificateChecks.KernelSporSch.M12S 5 CertificateChecks.KernelSporSch.M12MOC.tSM

#ks_rawchain CertificateChecks.KernelSporSch.M12DQ 24 5 16 CertificateChecks.KernelSporSch.M12MOC.SM
  CertificateChecks.KernelSporSch.M12MOC.baseM 2 CFSG.Sporadic.Schreier.m12Words

#ks_rawchain CertificateChecks.KernelSporSch.M12SC 24 5 16 CertificateChecks.KernelSporSch.M12MOC.SC
  CertificateChecks.KernelSporSch.M12MOC.baseC 3 CFSG.Sporadic.Schreier.m12SigmaCentChainWords

#kss_classes2 CertificateChecks.KernelSporSch.M12SCL 24 5 CertificateChecks.KernelSporSch.M12MOC.tAM
  CertificateChecks.KernelSporSch.M12MOC.tBM CertificateChecks.KernelSporSch.M12MOC.tA
  CertificateChecks.KernelSporSch.M12MOC.tB CertificateChecks.KernelSporSch.M12MOC.repsM 2 1000

namespace CertificateChecks.KernelSporSch.M12MOC

@[expose] noncomputable def A0 : Nat := M12DQ.S 0

@[expose] noncomputable def B0 : Nat := M12DQ.S 1

end CertificateChecks.KernelSporSch.M12MOC

#kss_odd CertificateChecks.KernelSporSch.M12SO CertificateChecks.KernelSporSch.M12SC 24 5
  CertificateChecks.KernelSporSch.M12MOC.SC CertificateChecks.KernelSporSch.M12MOC.baseC 15

#kss_cntord2 CertificateChecks.KernelSporSch.M12SX CertificateChecks.KernelSporSch.M12DQ 24 5
  CertificateChecks.KernelSporSch.M12MOC.SM CertificateChecks.KernelSporSch.M12MOC.baseM
  CertificateChecks.KernelSporSch.M12S CertificateChecks.KernelSporSch.M12MOC.tSM 2

#kss_cntcomm CertificateChecks.KernelSporSch.M12SZ CertificateChecks.KernelSporSch.M12DQ 24 5
  CertificateChecks.KernelSporSch.M12MOC.SM CertificateChecks.KernelSporSch.M12MOC.baseM
  CertificateChecks.KernelSporSch.M12S CertificateChecks.KernelSporSch.M12MOC.tSM
  CertificateChecks.KernelSporSch.M12MOC.A0 CertificateChecks.KernelSporSch.M12MOC.tAM
  CertificateChecks.KernelSporSch.M12MOC.B0 CertificateChecks.KernelSporSch.M12MOC.tBM

end

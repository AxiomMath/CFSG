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
public import CFSG.Certificates.Kernel.SporSch.ChainKCosetClassEq

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

namespace CertificateChecks.KernelSporSch.M12MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT

@[expose] noncomputable def XS : List Nat :=
  [M12S, 387153341893186120554281892352508462,
    262344533101702297390406748030457324, 345745483202643351704816408176806380,
    426136160660737035371432092000466380, 259817947195383774292938983637201330,
    345376767898781270660426056587558316, 469989423826469572283540002200766892,
    11893190894496210190204629591541164]

@[expose] noncomputable def CS : List Nat := [120, 24, 12, 6, 10, 10, 6, 6, 6]

theorem sRep0 : cosetRepC 24 5 (mask 5) (24 * 5) M12DQ.BP 5 M12DQ.LR M12DQ.TRI M12S
    (XS.getD 0 0) = true := by quickRfl

theorem sRepT : allN 8 (fun i => cosetRepK 24 5 (mask 5) (24 * 5) M12DQ.BP 5 M12DQ.LR M12DQ.TR
    M12DQ.TRI M12S (XS.getD (i + 1) 0) (CS.getD (i + 1) 0)) = true := by quickRfl

theorem sDist : allN 9 (fun i => allN i (fun j => distK 24 5 (mask 5) (24 * 5) M12DQ.BP 5
    M12DQ.LR M12DQ.TR M12DQ.TRI (XS.getD j 0) (XS.getD i 0))) = true := by quickRfl

theorem sSum : Nat.beq (sumAllK (ordK M12DQ.LR 5) CS 9) (ordK M12DQ.LR 5) = true := by quickRfl

theorem sLt : allN 9 (fun i => Nat.blt (CS.getD i 0) (ordK M12DQ.LR 5)) = true := by quickRfl

theorem sTot2 : Nat.beq (sumOrdK 24 5 (mask 5) (ordK M12DQ.LR 5) XS CS 2 9) 792 = true := by
  quickRfl

end CertificateChecks.KernelSporSch.M12MOC

end

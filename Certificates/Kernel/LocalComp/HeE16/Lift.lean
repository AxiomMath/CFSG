module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.Spor.PEnumX
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBE16Inputs
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBE16Inputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr
meta import CFSG.GroupTheory.LocalCores.Fitting
meta import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixTwoBStr

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeE16

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.HeldFix

meta def liftM : Array (Array Nat) := (List.range 6).toArray.map heLiftTab

end CertificateChecks.KernelLC.HeE16

#kmisc_packarrs CertificateChecks.KernelLC.HeE16.LP CertificateChecks.KernelLC.HeE16.liftM 14

namespace CertificateChecks.KernelLC.HeE16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CertificateChecks.KernelLC.HeFix
open CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def cm (a b : Nat) : Nat := pc (pc (pc (LP a) (LP b)) (LP a)) (LP b)

theorem kWords : allN 6 (fun i => Nat.beq (LP i)
    (wordTabK 8330 14 PC1 (CFSG.KS.PEnum.lget2 heRWords i))) = true := by
  quickRfl

theorem kInv : allN 6 (fun i => permOK 8330 14 (mask 14) (8330 * 14) (LP i) (LP i)) = true := by
  quickRfl

theorem kSq : allN 6 (fun i => Nat.beq (pc (LP i) (LP i)) (pidn 8330 14)) = true := by
  quickRfl

theorem kWithin : (Nat.beq (cm 0 1) (pidn 8330 14) && Nat.beq (cm 0 2) (pidn 8330 14) &&
    Nat.beq (cm 1 2) (pidn 8330 14) && Nat.beq (cm 3 4) (pidn 8330 14) &&
    Nat.beq (cm 3 5) (pidn 8330 14) && Nat.beq (cm 4 5) (pidn 8330 14)) = true := by
  quickRfl

theorem kCross : (Nat.beq (cm 0 3) PT1 && Nat.beq (cm 0 4) PT1 && Nat.beq (cm 0 5) PT1 &&
    Nat.beq (cm 1 3) PT1 && Nat.beq (cm 1 4) PT1 && Nat.beq (cm 1 5) (pidn 8330 14) &&
    Nat.beq (cm 2 3) (pidn 8330 14) && Nat.beq (cm 2 4) PT1 && Nat.beq (cm 2 5) PT1) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeE16

end

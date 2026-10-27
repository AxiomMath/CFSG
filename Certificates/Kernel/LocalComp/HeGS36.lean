module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.SporSch.HeT.B2114K
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHe36CertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeGS36

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.ComponentClassification.GrSLit.HeGS CertificateChecks.KernelLC.HeFix
open CFSG.Sporadic.SmallOddCore

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def K (w : List Nat) : Nat :=
  wordTabK 8330 14 CertificateChecks.KernelSporSch.HeB14.C0 w

@[expose] noncomputable def H (w : List Nat) : Nat := wordTabK 8330 14 PC1 w

@[expose] noncomputable def cT : Nat :=
  pc (powK 8330 14 (pc (pc (pc (HG.F 1) (K (heDWords.getD 1 []))) G1I) PT1) 8) (HG.F 1)

@[expose] noncomputable def cI : Nat := pinvS 8330 14 (mask 14) cT

@[expose] noncomputable def w1 : Nat := pc (pc cT (HG.F 0)) cI

@[expose] noncomputable def tgt (p : Nat) : Nat := nIf(Nat.beq (p % 2) 0, w1, pc w1 PT1)

@[expose] noncomputable def zT : Nat := pc (pc (pc G1I (HG.F 0)) (HG.F 1)) (K heGSVWord)

@[expose] noncomputable def gT : Nat := pc (pc zT zT) G1I

@[expose] noncomputable def gI : Nat := pinvS 8330 14 (mask 14) gT

@[expose] noncomputable def i5 : Nat := pc (pc gT (K (heDWords.getD 0 []))) gI

@[expose] noncomputable def wK (p : Nat) : Bool :=
  Nat.beq (H (heGS36D p 0 ++ heGS36D p 1)) (pidn 8330 14) &&
    Nat.beq (H (heGS36D p 2 ++ heGS36D p 3)) (pidn 8330 14) &&
      Nat.beq (H (heGS36Word p)) (tgt p)

theorem kCanon : (allN 9 (fun j => cn (CertificateChecks.KernelSporSch.HeB14.C0 j)) &&
    cn G1I && cn cT && cn cI && cn gT && cn gI) = true := by
  quickRfl

theorem kC : (Nat.beq (pc cT (K (heDWords.getD 1 []))) (pc PT1 cT) &&
    permOK 8330 14 (mask 14) (8330 * 14) cT cI && permOK 8330 14 (mask 14) (8330 * 14) cI cT &&
    permOK 8330 14 (mask 14) (8330 * 14) gT gI && permOK 8330 14 (mask 14) (8330 * 14) gI gT) =
      true := by
  quickRfl

theorem kW0 : wK 0 = true := by quickRfl

theorem kW1 : wK 1 = true := by quickRfl

theorem kW2 : wK 2 = true := by quickRfl

theorem kW3 : wK 3 = true := by quickRfl

theorem kE : (!Nat.beq (pc (K (heDWords.getD 1 [])) i5) (pc i5 (K (heDWords.getD 1 []))) &&
    Nat.beq (pc (K (heGSComm2 heGSUComm)) (K (heGSComm2 heGSUComm))) (pidn 8330 14)) = true := by
  quickRfl

end CertificateChecks.KernelLC.HeGS36

end

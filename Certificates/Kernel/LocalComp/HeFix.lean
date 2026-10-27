module

public import Certificates.Kernel.LocalComp.HeFixData
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixSylowCheckInputs
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.HeldB.CertPChainData
meta import CFSG.Sporadic.HeldB.AutData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000
set_option Elab.async false

#ks_chars CertificateChecks.KernelLC.HeFix.HG CFSG.Sporadic.HeldB.heGenHex
#kmisc_hexflat CertificateChecks.KernelLC.HeFix.HG CFSG.Sporadic.HeldB.heGenHex 4 8330 14 2
#ks_chars CertificateChecks.KernelLC.HeFix.HR CFSG.Sporadic.HeldB.heAutRHex
#kmisc_hexflat CertificateChecks.KernelLC.HeFix.HR CFSG.Sporadic.HeldB.heAutRHex 4 8330 14 1

namespace CertificateChecks.KernelLC.HeFix

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CFSG.KC.Misc.HexFlat CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.HeldB CFSG.ComponentClassification.GrSLit.HeldFix
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native

@[expose] noncomputable def L2 (j : Nat) : Nat := [HG.F 0, HG.F 1].getD j 0

@[expose] noncomputable def L2I (j : Nat) : Nat := [G0I, G1I].getD j 0

@[expose] noncomputable def L3 (j : Nat) : Nat := [HG.F 0, HG.F 1, PT1].getD j 0

@[expose] noncomputable def L3I (j : Nat) : Nat := [G0I, G1I, T1I].getD j 0

@[expose] noncomputable def LU (j : Nat) : Nat := [HG.F 0, HG.F 1, PU].getD j 0

@[expose] noncomputable def LUI (j : Nat) : Nat := [G0I, G1I, UI].getD j 0

@[expose] noncomputable def LY (j : Nat) : Nat := [PC1 0, PC1 1, PC1 2, PC1 3, PC1 4, PC1 5,
  PC1 6, PC1 7, PC1 8, PX].getD j 0

@[expose] noncomputable def T0K (j : Nat) : Nat :=
  [PT1, wordTabK 8330 14 PC1 (hfTauWords.getD 0 []), wordTabK 8330 14 PC1 (hfTauWords.getD 1 []),
    wordTabK 8330 14 PC1 (hfTauWords.getD 2 []), wordTabK 8330 14 PC1 (hfTauWords.getD 3 []),
    wordTabK 8330 14 LY hfYWord].getD j 0

@[expose] noncomputable def cn (p : Nat) : Bool := canonK 8330 14 (mask 14) (8330 * 14) p


theorem kCanonG : (cn (HG.F 0) && cn (HG.F 1) && cn (HR.F 0)) = true := by quickRfl

theorem kCanonW : (cn PT1 && cn PU && cn PX) = true := by quickRfl

theorem kCanonC : allN 9 (fun j => cn (PC1 j)) = true := by quickRfl

theorem kId : (cn (pidn 8330 14) && idK 8330 14 (mask 14)) = true := by quickRfl

theorem kPL2 : allN 2 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (L2 j) (L2I j)) = true := by
  quickRfl

theorem kPL3 : allN 3 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (L3 j) (L3I j)) = true := by
  quickRfl

theorem kPLU : allN 3 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (LU j) (LUI j)) = true := by
  quickRfl

theorem kT1 : wordEqK 8330 14 (mask 14) (pidn 8330 14) L2 L2I 2 heT1Word PT1 = true := by
  quickRfl

theorem kU : Nat.beq (powK 8330 14 (HR.F 0) 5) PU = true := by quickRfl

theorem kRes0 : Nat.beq (restrictK 14 6 hfDelta32 (T0K 0)) (Q 0) = true := by quickRfl

theorem kRes1 : Nat.beq (restrictK 14 6 hfDelta32 (T0K 1)) (Q 1) = true := by quickRfl

theorem kRes2 : Nat.beq (restrictK 14 6 hfDelta32 (T0K 2)) (Q 2) = true := by quickRfl

theorem kRes3 : Nat.beq (restrictK 14 6 hfDelta32 (T0K 3)) (Q 3) = true := by quickRfl

theorem kRes4 : Nat.beq (restrictK 14 6 hfDelta32 (T0K 4)) (Q 4) = true := by quickRfl

theorem kRes5 : Nat.beq (restrictK 14 6 hfDelta32 (T0K 5)) (Q 5) = true := by quickRfl

end CertificateChecks.KernelLC.HeFix

end

module

public import Certificates.Kernel.LocalComp.HeFix
public import Certificates.Kernel.LocalComp.HeFix2329.Enum
public import Certificates.Kernel.SporSch.HeT.B2114K
public import Certificates.Data.Kernel.LocalComp.ConjPin
public import Certificates.Data.HeNormWords
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeNorm

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.PermTool CFSG.KC.LocalComp.ConjPin
open CFSG.ComponentClassification.GrSLit.HeldFix CertificateChecks.KernelLC.HeFix
open CertificateChecks.KernelSporSch.HeB14 (C1 C1I)

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 8330 14 (mask 14) p q

@[expose] noncomputable def W (i : Nat) : Nat :=
  wordTabK 8330 14 C1 (Certificates.HeNorm.words.getD i [])

@[expose] noncomputable def WI (i : Nat) : Nat :=
  wordTabK 8330 14 C1I (Certificates.HeNorm.words.getD i []).reverse

@[expose] noncomputable def Hh (i j : Nat) : Nat := pc (WI j) (W i)

@[expose] noncomputable def HI (i j : Nat) : Nat := pc (WI i) (W j)

@[expose] noncomputable def R (i j k : Nat) : Nat :=
  restrictK 14 6 hfDelta32 (pc (pc (Hh i j) (T0K k)) (HI i j))

theorem kW : (allN 9 (fun j => cn (C1 j) && cn (C1I j)) &&
    allN 8 (fun i => permOK 8330 14 (mask 14) (8330 * 14) (W i) (WI i))) = true := by
  quickRfl

theorem kH : allN 8 (fun i => allN 8 fun j =>
    permOK 8330 14 (mask 14) (8330 * 14) (Hh i j) (HI i j)) = true := by
  quickRfl

@[expose] noncomputable def outK (X : Nat) : Bool :=
  !(allN 32 fun x => Nat.blt (pg 6 (mask 6) X x) 32)

@[expose] noncomputable def nK (i : Nat) : Bool :=
  allN 8 fun j => Nat.beq i j ||
    !(allN 5 fun k => !(outK (R i j k) || notInK 32 6 HeT32.N HeT32.T (R i j k)))

theorem kN0 : nK 0 = true := by quickRfl
theorem kN1 : nK 1 = true := by quickRfl
theorem kN2 : nK 2 = true := by quickRfl
theorem kN3 : nK 3 = true := by quickRfl
theorem kN4 : nK 4 = true := by quickRfl
theorem kN5 : nK 5 = true := by quickRfl
theorem kN6 : nK 6 = true := by quickRfl
theorem kN7 : nK 7 = true := by quickRfl

end CertificateChecks.KernelLC.HeNorm

end

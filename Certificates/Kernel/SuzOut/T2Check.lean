module

public import Certificates.Kernel.SuzOut.T2Chain
public import Certificates.Kernel.Sporadic.SuzInv.Text2
public import CFSG.Certificates.Kernel.PermToolSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

set_option maxRecDepth 400000
public section

namespace CertificateChecks.KernelSuzOut.T2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.SuzOut CFSG.KC.TitsPrim CFSG.KC.PermTool
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzOut

@[expose] noncomputable def L (x : Nat) : Nat := pg 9 (mask 9) (T2Lb 0) x

@[expose] noncomputable def R (j : Nat) : Nat := pg 11 (mask 11) (T2Rp 0) j

@[expose] noncomputable def Lc (p : Nat) : Nat := pg 4 (mask 4) (T2Lc 0) p

@[expose] noncomputable def Rc (j : Nat) : Nat := pg 9 (mask 9) (T2Rc 0) j

@[expose] noncomputable def abW : List (List Int) := wordsK T2AbC.chars

@[expose] noncomputable def A : Nat := T2D.S 0

@[expose] noncomputable def B : Nat := T2D.S 1

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 396 9 (mask 9) p q

theorem texts : (natsPK 9 (T2Lb 0) 1782 T2LabC.chars && natsPK 11 (T2Rp 0) 396 T2RepC.chars &&
    natsPK 4 (T2Lc 0) 396 T2LabelsC.chars && natsPK 9 (T2Rc 0) 10 T2RootsC.chars &&
    intLinesOK (bodyK T2AbC.chars) && intLinesOK (bodyK T2XwC.chars) &&
    intLinesOK (bodyK T2DwC.chars)) = true := by
  quickRfl

theorem reps : repsK 1782 396 L R = true := by quickRfl

theorem block0 : blockK 1782 11 396 9 (SuzInvT2.F 12) (T2X.S 0) (T2X.SI 0) L R = true := by
  quickRfl

theorem block1 : blockK 1782 11 396 9 (SuzInvT2.F 13) (T2X.S 1) (T2X.SI 1) L R = true := by
  quickRfl

theorem permsX : allN 7 (fun j => permOK 396 9 (mask 9) (396 * 9) (T2X.S j) (T2X.SI j)) = true := by
  quickRfl

theorem permsD : allN 6 (fun j => permOK 396 9 (mask 9) (396 * 9) (T2D.S j) (T2D.SI j)) = true := by
  quickRfl

theorem letters : (Nat.beq abW.length 2 && lettersK 2 (abW.getD 0 []) &&
    lettersK 2 (abW.getD 1 [])) = true := by
  quickRfl

theorem abOK : (allN 396 (fun y => Nat.beq (pg 9 (mask 9) A y) (ptK 9 T2X.S T2X.SI (abW.getD 0 []) y)) &&
    allN 396 (fun y => Nat.beq (pg 9 (mask 9) B y) (ptK 9 T2X.S T2X.SI (abW.getD 1 []) y))) =
    true := by
  quickRfl

theorem prim : walkK 396 (primOK 9 6 396 10 0 T2D.S T2D.SI Lc Rc) (bodyK T2TwC.chars)
    (bodyK T2HwC.chars) 0 = true := by
  quickRfl

theorem reach : reachWalkK 9 6 396 10 0 T2D.S T2D.SI Lc Rc (bodyK T2TwC.chars)
    (bodyK T2ReC.chars) = true := by
  quickRfl

theorem relA : relK 396 9 60 A T2Rw = true := by quickRfl

theorem relB : relK 396 9 60 B T2Rw = true := by quickRfl

theorem move : moveK 396 9 60 (T2X.S 0) T2Rw 0 0 = true := by quickRfl

theorem ordA : (Nat.beq (powK 396 9 A 3) (pidn 396 9) && !Nat.beq A (pidn 396 9)) = true := by
  quickRfl

theorem ordB : (Nat.beq (powK 396 9 B 11) (pidn 396 9) && !Nat.beq B (pidn 396 9)) = true := by
  quickRfl

theorem ordAB : (Nat.beq (powK 396 9 (pc A B) 11) (pidn 396 9) &&
    !Nat.beq (pc A B) (pidn 396 9)) = true := by
  quickRfl

theorem comm : (!Nat.beq (pc A B) (pc B A)) = true := by quickRfl

end CertificateChecks.KernelSuzOut.T2

end

module

public import Certificates.Kernel.SuzOut.T3Data
public import Certificates.Kernel.Sporadic.SuzInv.Text3
public import CFSG.Certificates.Kernel.PermToolSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

set_option maxRecDepth 400000
public section

namespace CertificateChecks.KernelSuzOut.T3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.SuzOut CFSG.KC.TitsPrim CFSG.KC.PermTool
open CertificateChecks.KernelSpor CertificateChecks.KernelSuzOut

@[expose] noncomputable def fixL : List Nat := (List.range 100).map (pg 11 (mask 11) (T3Fx 0))

@[expose] noncomputable def Lc (p : Nat) : Nat := pg 2 (mask 2) (T3Lc 0) p

@[expose] noncomputable def Rc (j : Nat) : Nat := pg 7 (mask 7) (T3Rc 0) j

@[expose] noncomputable def abW : List (List Int) := wordsK T3AbC.chars

@[expose] noncomputable def A : Nat := T3D.S 0

@[expose] noncomputable def B : Nat := T3D.S 1

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 100 7 (mask 7) p q

theorem texts : (natsPK 2 (T3Lc 0) 100 T3LabelsC.chars && natsPK 7 (T3Rc 0) 3 T3RootsC.chars &&
    intLinesOK (bodyK T3AbC.chars) && intLinesOK (bodyK T3XwC.chars) &&
    intLinesOK (bodyK T3DwC.chars)) = true := by
  quickRfl

theorem kRes : allN 5 (fun j => canonK 1782 11 (mask 11) (1782 * 11) (SuzInvT3.F (Nat.add 20 j)) &&
    Nat.beq (restrictK 11 7 fixL (SuzInvT3.F (Nat.add 20 j))) (T3X.S j)) = true := by
  quickRfl

theorem letters : (Nat.beq abW.length 2 && lettersK 5 (abW.getD 0 []) &&
    lettersK 5 (abW.getD 1 [])) = true := by
  quickRfl

theorem abOK : (allN 100 (fun y => Nat.beq (pg 7 (mask 7) A y) (ptK 7 T3X.S T3X.SI (abW.getD 0 []) y)) &&
    allN 100 (fun y => Nat.beq (pg 7 (mask 7) B y) (ptK 7 T3X.S T3X.SI (abW.getD 1 []) y))) =
    true := by
  quickRfl

theorem prim : walkK 100 (primOK 7 7 100 3 0 T3D.S T3D.SI Lc Rc) (bodyK T3TwC.chars)
    (bodyK T3HwC.chars) 0 = true := by
  quickRfl

theorem reach : reachWalkK 7 7 100 3 0 T3D.S T3D.SI Lc Rc (bodyK T3TwC.chars)
    (bodyK T3ReC.chars) = true := by
  quickRfl

theorem ordA : (Nat.beq (powK 100 7 A 3) (pidn 100 7) && !Nat.beq A (pidn 100 7)) = true := by
  quickRfl

theorem ordB : (Nat.beq (powK 100 7 B 7) (pidn 100 7) && !Nat.beq B (pidn 100 7)) = true := by
  quickRfl

theorem ordAB : (Nat.beq (powK 100 7 (pc A B) 5) (pidn 100 7) &&
    !Nat.beq (pc A B) (pidn 100 7)) = true := by
  quickRfl

theorem comm : (!Nat.beq (pc A B) (pc B A)) = true := by quickRfl

end CertificateChecks.KernelSuzOut.T3

end

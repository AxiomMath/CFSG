module

public import Certificates.Kernel.RuThree.K
public import Certificates.Kernel.RuThree.ClassData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def commV (j i : Nat) : Bool :=
  eqOnL bs (fun b => cv j (cv i b)) (fun b => cv i (cv j b))

@[expose] noncomputable def countK (i : Nat) : Nat := (List.range 2160).countP fun j => commV j i

@[expose] noncomputable def conjOK (g i r : Nat) : Bool :=
  eqOnL bs (fun b => cv g (cv i b)) (fun b => cv r (cv g b))

@[expose] noncomputable def wg (i : Nat) : Nat := CW.getD i 0 / 256

@[expose] noncomputable def wt (i : Nat) : Nat := CW.getD i 0 % 256

@[expose] noncomputable def witOK (i m : Nat) : Bool :=
  Nat.blt (wg i) 2160 && Nat.blt (wt i) 2 && Nat.blt (RR.getD (wt i) 0) 2160 &&
    conjOK (wg i) i (RR.getD (wt i) 0) && Nat.blt (RC.getD (wt i) 0 * m) 2160

@[expose] noncomputable def classAt (i : Nat) : Bool :=
  eqOnL bs (cv i) (fun x => x) ||
    ((!eqOnL bs (powF (cv i) 2) (fun x => x) || witOK i 16) &&
      (!eqOnL bs (powF (cv i) 5) (fun x => x) || witOK i 80))

theorem kCount0 : Nat.beq (countK (RR.getD 0 0)) (RC.getD 0 0) = true := by quickRfl

theorem kCount1 : Nat.beq (countK (RR.getD 1 0)) (RC.getD 1 0) = true := by quickRfl

theorem kClass0 : allN 540 (fun j => classAt (Nat.add (Nat.mul 540 0) j)) = true := by quickRfl

theorem kClass1 : allN 540 (fun j => classAt (Nat.add (Nat.mul 540 1) j)) = true := by quickRfl

theorem kClass2 : allN 540 (fun j => classAt (Nat.add (Nat.mul 540 2) j)) = true := by quickRfl

theorem kClass3 : allN 540 (fun j => classAt (Nat.add (Nat.mul 540 3) j)) = true := by quickRfl

end CertificateChecks.KernelRuThree

end

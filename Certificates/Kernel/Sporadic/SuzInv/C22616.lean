module

public import Certificates.Kernel.Sporadic.SuzInv.Text0
public import Certificates.Kernel.Sporadic.SuzInv.Text1
public import Certificates.Kernel.Sporadic.SuzInv.Text2
public import Certificates.Kernel.Sporadic.SuzInv.Text3
public import Certificates.Data.Kernel.SporSch.SporXElem
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.SuzInv.C22616

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporXE CFSG.KS.SporSch CertificateChecks.KernelSpor

@[expose] noncomputable def ptsL (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun k ih => k :: ih) n

@[expose] noncomputable def lE (F : Nat → Nat) (s l x : Nat) : Nat :=
  pg 11 (mask 11) (F (Nat.add s l)) x

@[expose] def w0 : List (List Nat × Nat) := [([0], 1), ([1], 1), ([14], 2), ([16, 18, 21], 2)]

@[expose] def w1 : List (List Nat × Nat) := [([0], 1), ([1], 1), ([1, 6, 8, 6], 2), ([8, 6, 1], 3)]

@[expose] def w2 : List (List Nat × Nat) :=
  [([1, 0, 0, 1, 0], 2), ([0, 0, 1, 0], 3), ([0, 0, 1, 0, 1], 2)]

@[expose] def w3 : List (List Nat × Nat) := [([0], 1), ([1, 2, 1, 2, 1], 1), ([2, 4, 2, 4, 3], 2)]

theorem ck0 : ckE (ptsL 1782) (lE SuzInvT0.F 32) 22 w0 = true := by quickRfl

theorem ck1 : ckE (ptsL 1782) (lE SuzInvT1.F 18) 10 w1 = true := by quickRfl

theorem ck2 : ckE (ptsL 1782) (lE SuzInvT2.F 12) 2 w2 = true := by quickRfl

theorem ck3 : ckE (ptsL 1782) (lE SuzInvT3.F 20) 5 w3 = true := by quickRfl

end CFSG.KD.SuzInv.C22616

end

module

public import Certificates.Data.Kernel.SporSch.SporXElem
public import Certificates.Kernel.SporSch.PairHS.HS2272Fns
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.HS3850.C22614

open CFSG.KS.SporXE CertificateChecks.KernelSporSch.HS72

@[expose] def w0 : List (List Nat × Nat) :=
  [([1, 1, 1, 1, 1, 0, 0, 0, 1], 5), ([0, 1, 0, 1, 0, 0, 1, 0, 0], 2), ([1, 0, 0], 2),
    ([0, 0, 1, 0, 0, 1, 0, 1, 0], 1)]

@[expose] def w1 : List (List Nat × Nat) :=
  [([2, 3, 0], 1), ([2, 2, 1, 0, 0, 0, 1, 3, 2, 0, 2, 2], 2), ([2, 3, 1, 2, 0, 2], 5),
    ([3, 3, 1, 1, 0, 1, 0, 1, 0, 0, 1, 2], 4)]

@[expose] def w2 : List (List Nat × Nat) :=
  [([2, 2, 1, 0], 2), ([1, 2], 6), ([0, 0, 1, 3, 3, 1], 2)]

@[expose] def w3 : List (List Nat × Nat) :=
  [([2, 3, 0, 0, 2], 1), ([3, 2], 1), ([0, 2, 3, 0, 2], 6)]

@[expose] noncomputable def lr (c l x : Nat) : Nat := tv (Nat.add c l) x

theorem ck0 : ckE bsR (lr 6) 2 w0 = true := by quickRfl

theorem ck1 : ckE bsR (lr 13) 4 w1 = true := by quickRfl

theorem ck2 : ckE bsR (lr 22) 4 w2 = true := by quickRfl

theorem ck3 : ckE bsR (lr 35) 4 w3 = true := by quickRfl

end CFSG.KD.HS3850.C22614

end

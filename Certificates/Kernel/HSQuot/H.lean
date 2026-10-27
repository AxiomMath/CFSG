module

public import Certificates.Kernel.HSQuot.D
public import Certificates.Kernel.LocalQT.HS4089.L
public import Certificates.Data.Kernel.LocalQT.QuotS
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.LocalQT.PcOm

set_option maxRecDepth 100000

public section

namespace CFSG.KD.HSQuot

open CFSG.KC.LQT.QS

@[expose] def xs1 : List (List Nat × Nat × Nat) :=
  [([2, 2, 2, 0, 3, 1, 1, 2, 0, 0, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3, 3, 3, 1, 0, 2, 3, 2, 0, 2, 3, 3, 0,
    0, 1, 3, 2, 3, 0, 0, 3, 1, 0, 0, 3, 3, 1, 2, 3, 2, 0, 3, 0, 3, 3, 3, 2, 2, 3, 2, 2], 4, 3),
   ([2, 3, 0, 1, 3, 0, 2, 2, 2, 2, 2, 1, 1, 1, 3, 0, 2, 0, 1, 1, 3, 0, 3, 0, 2, 2, 1, 0, 3, 3, 1, 1,
    3, 1, 2, 1, 0, 0, 2, 1, 2, 0, 1, 2, 1, 1, 1, 1, 1, 2, 0, 3, 0, 2, 3, 3, 3, 0, 0, 2], 2, 5)]

@[expose] def xs2 : List (List Nat × Nat × Nat) :=
  [([0, 2, 2, 1, 2, 3, 1, 2, 0, 3, 2, 1, 1, 2, 0, 3, 1, 1, 1, 0, 1, 2, 2, 0, 3, 2, 0, 3, 0, 0, 1, 1],
    1, 7),
   ([3, 2, 0, 0, 0, 3, 0, 3, 1, 0, 2, 1, 0, 3, 0, 0], 4, 3),
   ([1, 3, 3, 2, 0, 0, 3, 1, 1, 1, 1, 2, 2, 1, 0, 2, 3], 2, 3)]

@[expose] noncomputable def LC1 : List Nat :=
  [CFSG.KD.LQT.H4089S.TF 172, CFSG.KD.LQT.H4089S.TF 185, CFSG.KD.LQT.H4089S.TF 200,
    CFSG.KD.LQT.H4089.TF 1]

@[expose] noncomputable def LC2 : List Nat :=
  [CFSG.KD.LQT.H4089S.TF 172, CFSG.KD.LQT.H4089S.TF 185, CFSG.KD.LQT.H4089S.TF 200,
    CFSG.KD.LQT.H4089.TF 2]

theorem hd1 : quotSK 1100 11 [0, 1, 2] LC1 xs1 18 RT1 3840 12 1000000 E1 PG1 15 256 3840 = true := by
  quickRfl

theorem hd2 : quotSK 1100 11 [0, 1, 2] LC2 xs2 18 RT2 10752 14 1000000 E2 PG2 42 256 10752 =
    true := by
  quickRfl

end CFSG.KD.HSQuot

end

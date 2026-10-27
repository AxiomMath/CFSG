module

public import Certificates.Kernel.LocalQT.Quot.D4080
public import Certificates.Kernel.LocalQT.Base.C4143D
public import Certificates.Data.Kernel.LocalQT.QuotS
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4080

open CFSG.KC.LQT.QS

@[expose] def mw : List Nat := [0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0]

@[expose] def xs : List (List Nat × Nat × Nat) :=
  [([3, 3, 2, 2, 0, 3, 0, 1, 2, 3, 1, 2, 2, 0, 2, 1, 3], 8, 3),
   ([1, 3, 0, 1, 1, 0, 1, 3, 1, 3, 1, 2, 3, 0, 0, 2, 2, 0, 0, 2, 1, 3, 2, 0, 1, 2], 4, 3)]

@[expose] noncomputable def LC : List Nat :=
  [CFSG.KD.LQT.C4143.TF 163, CFSG.KD.LQT.C4143.TF 172, CFSG.KD.LQT.C4143.TF 185,
    wordC 4060 12 [CFSG.KD.LQT.C4143.TF 0, CFSG.KD.LQT.C4143.TF 1] mw]

theorem hd : quotSK 4060 12 [0, 1, 2, 3, 4] LC xs 64 RT 122880 17 1000000 E PG 120 1024 122880 =
    true := by
  quickRfl

end CFSG.KD.LQT.C4080

end

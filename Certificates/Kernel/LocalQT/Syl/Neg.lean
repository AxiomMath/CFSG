module

public import Certificates.Data.Kernel.LocalQT.SylL
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.SylNeg

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.Syl

@[expose] noncomputable def a : Nat := swap 4 0 1
@[expose] noncomputable def b : Nat := swap 4 2 3
@[expose] noncomputable def V : List Nat := lstK 4 2 [a, b]

theorem elt1 : Nat.beq (eltK 4 2 [a, b] 1) a = true := by quickRfl
theorem elt2 : Nat.beq (eltK 4 2 [a, b] 2) b = true := by quickRfl
theorem elt3 : Nat.beq (eltK 4 2 [a, b] 3) (mul 4 a b) = true := by quickRfl
theorem eab_ok : eabK 4 2 [a, b] = true := by quickRfl
theorem eab_rep : notB (eabK 4 2 [a, a]) = true := by quickRfl
theorem syl_ok : sylG2K 4 2 V [a] = true := by quickRfl
theorem syl_out : notB (sylG2K 4 2 V [swap 4 0 2]) = true := by quickRfl
theorem rank_ok : rankK 4 (invK 4 V) 3 = true := by quickRfl
theorem rank_low : notB (rankK 4 (invK 4 V) 2) = true := by quickRfl
theorem cov_ok : g1covK 4 V [(1, [], []), (2, [], []), (3, [], [])] [(0, 0), (1, 0), (2, 0)] =
    true := by quickRfl
theorem cov_wrong : notB (g1covK 4 V [(1, [], []), (2, [], []), (3, [], [])]
    [(1, 0), (1, 0), (2, 0)]) = true := by quickRfl
theorem cov_short : notB (g1covK 4 V [(1, [], []), (2, [], []), (3, [], [])] [(0, 0), (1, 0)]) =
    true := by quickRfl
theorem bad_all : atMost (badK 4 V [(1, 2, [], [])] [(1023, 0), (1023, 0), (1023, 0), (1023, 0),
    (1023, 0), (1023, 0)]) 6 = true := by quickRfl
theorem bad_low : notB (atMost (badK 4 V [(1, 2, [], [])] [(1023, 0), (1023, 0), (1023, 0),
    (1023, 0), (1023, 0), (1023, 0)]) 5) = true := by quickRfl
theorem bad_fail : notB (atMost (badK 4 V [(1, 2, [], [])] [(1023, 0), (0, 0), (1023, 0),
    (1023, 0), (1023, 0), (1023, 0)]) 6) = true := by quickRfl
theorem bad_hit : atMost (badK 4 V [(1, 2, [], [])] [(0, 0), (1023, 0), (1023, 0), (1023, 0),
    (1023, 0), (1023, 0)]) 5 = true := by quickRfl
theorem chunk : (chunkK (3 * 1024 + 5 + (7 * 1024 + 1) * 1048576)).take 2 = [(3, 5), (7, 1)] := by
  decide +kernel

end CFSG.KD.LQT.SylNeg

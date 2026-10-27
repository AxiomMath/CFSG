module

public import Certificates.Kernel.L34Four.Data
public import Certificates.Data.Kernel.L34Four
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.L34Four

@[expose] def w2 : List (List Nat) := [[0], [1], [4], [5]]

@[expose] def w3 : List (List Nat) := [[0], [4], [5], [1, 5, 1, 5, 1], [1, 5, 2, 5, 1]]

theorem row2_ok : rowL G6 4 w2 Gc2 Gci2 [0, 1] 7 [3, 7] R2 48 = true := by
  quickRfl

theorem row3_ok : rowL G6 5 w3 Gc3 Gci3 [0, 4] 5 [0, 1] R3 24 = true := by
  quickRfl

end CFSG.KD.L34Four

end

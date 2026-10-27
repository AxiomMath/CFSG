module

public import Certificates.Kernel.StdOdd.Sylow57
public import Certificates.Data.Kernel.Misc.E6ConjOrb
import all CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Comm7B

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std CFSG.KD.StdOdd.Reps
  CFSG.KD.StdOdd.Sylow57 CFSG.Monster.Existence.StdOdd.Cert CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel

set_option maxRecDepth 100000

@[expose] def steps7B : List (ℕ × ℕ) := [(0, 0), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (4, 1),
  (5, 0), (5, 1), (6, 0), (6, 1), (7, 0), (7, 1), (8, 0), (9, 0), (9, 1), (10, 0), (11, 0), (11, 1),
  (12, 1), (13, 0), (14, 0), (15, 1)]

@[expose] noncomputable def hB : ℕ := wordB (nthV Fvals idxA) (nthV Fvals idxB) b7B

@[expose] noncomputable def tB : ℕ := powB hB 7

theorem ch17105t : Nat.beq (powB tB 4) oneB = true := by quickRfl

theorem ch17105orb : conjOrbK tB (powB tB 3) z7 (powB z7 6) steps7B z7 = true := by quickRfl

end CFSG.KD.StdOdd.Comm7B

end

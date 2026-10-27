module

public import Certificates.Kernel.StdOdd.Sylow57
public import Certificates.Kernel.StdOdd.Cent7.Data
public import Certificates.Data.Kernel.Misc.E6SubClos
import all CFSG.Monster.Existence.StdOdd.Cert.Sylow57Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent7

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std CFSG.KD.StdOdd.Reps
  CFSG.KD.StdOdd.Sylow57 CFSG.Monster.Existence.StdOdd.Cert CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel

set_option maxRecDepth 100000

@[expose] noncomputable def gA : ℕ := wordB (nthV Fvals idxA) (nthV Fvals idxB) b7A

@[expose] noncomputable def y5A : ℕ := powB gA 7

@[expose] noncomputable def cA : ℕ := nthV S7.V 192

@[expose] noncomputable def zpA : ℕ := mulB (mulB (powB cA 23) x7) cA

@[expose] noncomputable def lettersA : List ℕ := [y5A, powB y5A 4, zpA, powB zpA 6]

@[expose] noncomputable def dB : ℕ := nthV S7.V 87

@[expose] noncomputable def lB : ℕ := mulB (mulB (powB dB 11) x7) dB

@[expose] noncomputable def lettersB : List ℕ := [z7, powB z7 6, lB, powB lB 6]

theorem ch17104zA : letB zpA (fun z => Nat.beq (mulB xa7 z) (mulB z xa7)) = true := by quickRfl

theorem ch17104zB : letB lB (fun l => Nat.beq (mulB x7 l) (mulB l x7)) = true := by quickRfl

theorem ch17104A : invClassK lettersA twA 1 qwA qstepsA stepsA 1 5 = true := by quickRfl

theorem ch17104B : invClassK lettersB twB 14 qwB qstepsB stepsB 1 3 = true := by quickRfl

end CFSG.KD.StdOdd.Cent7

end

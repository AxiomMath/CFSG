module

public import Certificates.Kernel.StdOdd.RootOrbitData
public import Certificates.Kernel.StdOdd.RootOrbitCheckCmd
public import Certificates.Data.Kernel.Misc.E6Std
public import Certificates.Kernel.Misc.E6StdData
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KD.StdOdd.Orbit

open CFSG.KC.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel

@[expose] noncomputable def AM : Nat := nthV CFSG.KD.Misc.E6Std.Fvals idxA

@[expose] noncomputable def BM : Nat := nthV CFSG.KD.Misc.E6Std.Fvals idxB

theorem lenOK : Nat.beq (lenN RO.PL) 156 = true := by quickRfl

theorem rOK : Nat.blt RO.r 3968055 = true := by quickRfl

theorem rootOK' : rootOK RO.PL RO.r = true := by quickRfl

theorem sortOK' : sortOK RO.PL 3968055 = true := by quickRfl

theorem validA : stagesOK RO.DS RO.MA = true := by quickRfl

theorem validB : stagesOK RO.DS RO.MB = true := by quickRfl

theorem fullA : Nat.beq (net RO.DS RO.MA (full 3968055)) (full 3968055) = true := by quickRfl

theorem fullB : Nat.beq (net RO.DS RO.MB (full 3968055)) (full 3968055) = true := by quickRfl

theorem start : Nat.beq (nthN RO.RS 0) (Nat.shiftLeft 1 RO.r) = true := by quickRfl

theorem last : Nat.beq (nthN RO.RS RO.D) (full 3968055) = true := by quickRfl

#e6_orbit_checks RO AM BM

end CFSG.KD.StdOdd.Orbit

end

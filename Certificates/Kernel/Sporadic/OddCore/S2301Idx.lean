module

public import CFSG.Sporadic.SuzOddCore.InvArrays

public section

namespace CertificateChecks.KernelSpor.S2301

open CFSG.Sporadic.SuzOddCore

@[expose] def initLen (i : Nat) : Nat := (invInitRefinements.getD i []).length

@[expose] def nSteps (i : Nat) : Nat := (invSteps.getD i []).length

@[expose] def rounds (i s : Nat) : Nat := ((invSteps.getD i []).getD s []).getD 2 0

@[expose] def point (i s : Nat) : Nat := ((invSteps.getD i []).getD s []).getD 0 0

@[expose] def bound (i s : Nat) : Nat := ((invSteps.getD i []).getD s []).getD 1 0

@[expose] def sIdx (a i : Nat) : Nat → Nat
  | 0 => a + initLen i
  | s + 1 => sIdx a i s + 1 + rounds i s

@[expose] def caseStart : Nat → Nat
  | 0 => 0
  | i + 1 => sIdx (caseStart i) i (nSteps i) + 1

@[expose] def stageIdx (i s : Nat) : Nat := sIdx (caseStart i) i s

end CertificateChecks.KernelSpor.S2301

end

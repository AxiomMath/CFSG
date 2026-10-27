module

public import CFSG.RankThree.Native.SuzFiveData

public section

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native

@[expose] def initLen (i : Nat) : Nat := suzFiveInit[i]!

@[expose] def nSteps (i : Nat) : Nat := suzFiveSteps[i]!.length

@[expose] def rounds (i s : Nat) : Nat := (suzFiveSteps[i]!.getD s (0, 0, 0)).2.2

@[expose] def point (i s : Nat) : Nat := (suzFiveSteps[i]!.getD s (0, 0, 0)).1

@[expose] def bound (i s : Nat) : Nat := (suzFiveSteps[i]!.getD s (0, 0, 0)).2.1

@[expose] def sIdx (a i : Nat) : Nat → Nat
  | 0 => a + initLen i
  | s + 1 => sIdx a i s + 1 + rounds i s

@[expose] def caseStart : Nat → Nat
  | 0 => 0
  | i + 1 => sIdx (caseStart i) i (nSteps i) + 1

@[expose] def stageIdx (i s : Nat) : Nat := sIdx (caseStart i) i s

end CertificateChecks.KernelSpor.S8147

end

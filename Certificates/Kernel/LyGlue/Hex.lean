module

public import CFSG.Sporadic.Recognition.LyonsModelInputs
public import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Spor.Chain
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def cLf0 : Nat := Ly0.cB0
@[expose] noncomputable def cLf1 : Nat := Ly0.cB1
@[expose] noncomputable def cLf2 : Nat := Ly0.cB2
@[expose] noncomputable def cLf3 : Nat := Ly0.cB3
@[expose] noncomputable def cLf4 : Nat := Ly0.cB4
@[expose] noncomputable def cLf5 : Nat := Ly0.cB5
@[expose] noncomputable def cLf6 : Nat := Ly0.cB6
@[expose] noncomputable def cLf7 : Nat := Ly0.cB7
@[expose] noncomputable def cLf8 : Nat := Ly0.cB8
@[expose] noncomputable def cLf9 : Nat := Ly0.cB9
@[expose] noncomputable def cLf10 : Nat := Ly0.cB10
@[expose] noncomputable def cLf11 : Nat := Ly0.cB11
@[expose] noncomputable def cLf12 : Nat := Ly0.cB12
@[expose] noncomputable def cLf13 : Nat := Ly0.cB13
@[expose] noncomputable def cLf14 : Nat := Ly0.cB14

@[expose] noncomputable def dLf0 : Nat := Ly0.dB0
@[expose] noncomputable def dLf1 : Nat := Ly0.dB1
@[expose] noncomputable def dLf2 : Nat := Ly0.dB2
@[expose] noncomputable def dLf3 : Nat := Ly0.dB3
@[expose] noncomputable def dLf4 : Nat := Ly0.dB4
@[expose] noncomputable def dLf5 : Nat := Ly0.dB5
@[expose] noncomputable def dLf6 : Nat := Ly0.dB6
@[expose] noncomputable def dLf7 : Nat := Ly0.dB7
@[expose] noncomputable def dLf8 : Nat := Ly0.dB8
@[expose] noncomputable def dLf9 : Nat := Ly0.dB9
@[expose] noncomputable def dLf10 : Nat := Ly0.dB10
@[expose] noncomputable def dLf11 : Nat := Ly0.dB11
@[expose] noncomputable def dLf12 : Nat := Ly0.dB12
@[expose] noncomputable def dLf13 : Nat := Ly0.dB13
@[expose] noncomputable def dLf14 : Nat := Ly0.dB14

end CertificateChecks.KernelLy

#kc_select CertificateChecks.KernelLy CS cLf 15
#kc_select CertificateChecks.KernelLy DS dLf 15

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Recognition.LyonsSims

@[expose] noncomputable def cL (a : Nat) : Nat :=
  CFSG.KC.Enum.pg 17 (CFSG.KS.mask 17) (CS (Nat.div a 4455)) (Nat.mod a 4455)

@[expose] noncomputable def dL (a : Nat) : Nat :=
  CFSG.KC.Enum.pg 17 (CFSG.KS.mask 17) (DS (Nat.div a 4455)) (Nat.mod a 4455)

theorem cS_eq {k : Nat} (hk : k < 15) : CS k = Ly0.cBlks[k]! := by
  interval_cases k <;> rfl

theorem dS_eq {k : Nat} (hk : k < 15) : DS k = Ly0.dBlks[k]! := by
  interval_cases k <;> rfl

end CertificateChecks.KernelLy

end

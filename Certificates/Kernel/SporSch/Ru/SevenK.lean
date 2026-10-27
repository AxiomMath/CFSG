module

public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Data.Kernel.SporSch.RuK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSeven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 4060 12 (mask 12) p q

@[expose] noncomputable def B2 : Nat := pc A1 A1

@[expose] noncomputable def B2I : Nat := pc A1I A1I

@[expose] noncomputable def CA1 : Nat := pc A0 A1
@[expose] noncomputable def CA2 : Nat := pc CA1 A0I
@[expose] noncomputable def CA : Nat := pc CA2 A1I

@[expose] noncomputable def CB1 : Nat := pc B2 A0
@[expose] noncomputable def CB2 : Nat := pc CB1 B2I
@[expose] noncomputable def CB : Nat := pc CB2 A0I

@[expose] noncomputable def ce (p q r : Nat) : Bool := compEqK 4060 12 (mask 12) (4060 * 12) p q r

@[expose] noncomputable def sevenK (p : Nat) : Bool :=
  bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) p 7 (pidn 4060 12),
    neK 4060 12 (mask 12) (4060 * 12) p (pidn 4060 12))

theorem perm0 : permOK 4060 12 (mask 12) (4060 * 12) A0 A0I = true := by quickRfl
theorem perm1 : permOK 4060 12 (mask 12) (4060 * 12) A1 A1I = true := by quickRfl

theorem a1 : ce A0 A1 CA1 = true := by quickRfl
theorem a2 : ce CA1 A0I CA2 = true := by quickRfl
theorem a3 : ce CA2 A1I CA = true := by quickRfl
theorem b1 : ce A1 A1 B2 = true := by quickRfl
theorem b2 : ce A1I A1I B2I = true := by quickRfl
theorem b3 : ce B2 A0 CB1 = true := by quickRfl
theorem b4 : ce CB1 B2I CB2 = true := by quickRfl
theorem b5 : ce CB2 A0I CB = true := by quickRfl

theorem sevenA : sevenK CA = true := by quickRfl

theorem sevenB : sevenK CB = true := by quickRfl

end CertificateChecks.KernelSporSch.RuSeven

end

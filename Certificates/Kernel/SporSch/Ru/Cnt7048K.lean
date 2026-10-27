module

public import Certificates.Kernel.SporSch.Ru.Cnt7045K
public import Certificates.Kernel.SporSch.Ru.F7046K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Ru7048

open CFSG.KC.Enum CFSG.KS CFSG.KS.RowTree CFSG.KS.RuTree CFSG.KLC.Fi22 CFSG.KS.SporSch
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.Ru7045

@[expose] noncomputable def cntD (v : Nat) : Nat := popK (Nat.land (Row (nat_lit 0)) (Row v)) (nat_lit 4060)

@[expose] noncomputable def cntC (v : Nat) : Nat :=
  popK (Nat.land (Nat.land (Row (nat_lit 0)) (Row (nat_lit 1))) (Row v)) (nat_lit 4060)

@[expose] noncomputable def labOK (m : Nat) : Bool :=
  sB (Nat.land (Row (nat_lit 0)) (Row (nat_lit 1))) (fun M =>
    allN (nat_lit 4060) (fun x => eqB (bt M x) (bt m (F7046.Lf x))))

theorem kD1 : cntD 1 = 730 := by decide +kernel

theorem kDG : cntD 2808 = 780 := by decide +kernel

theorem kLab : labOK 196 = true := by quickRfl

theorem kL : F7046.Lf 2325 = 7 ∧ F7046.Lf 149 = 6 ∧ F7046.Lf 2 = 2 := by decide +kernel

theorem kC : cntC 2325 = 217 ∧ cntC 149 = 345 ∧ cntC 2 = 281 := by decide +kernel

end CertificateChecks.KernelSporSch.Ru7048

end

module

public import Certificates.Kernel.MonsterExist.ELevel.Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Monster.Existence.ELevelNativeInputs
public import Certificates.Kernel.MonsterExist.ELevel.Data

public section

set_option maxRecDepth 100000
set_option Elab.async false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ELevel

open CFSG.KC CFSG.KC.Loop CFSG.Monster CFSG.Monster.B CFSG.Monster.Existence
  CFSG.Monster.B.TwoA.Census CertificateChecks.MonsterExist.ShortKey CertificateChecks.MonsterExist.Eb

theorem perm1 : PermArr (cosetArr 1) = true := by decide +kernel
theorem aut1 : AutArr (cosetArr 1) := by decide +kernel
theorem basis1 : BasisOK 1 TB1 DB1 := by unfold BasisOK; decide +kernel
theorem tt1 : ttOK TB1 DB1 FB1 TT1 = true := by quickRfl
theorem xw1 : packP (wP 1) = 0 := by decide +kernel
theorem sw1 : synL FB1 0 = 0 := by decide +kernel
theorem elim1 : elimGo (fun x => x ^^^ kapL TB1 DB1 x) 24 [] [] = (PIV1, FB1) := by decide +kernel
theorem fb1 : ∀ f ∈ FB1, kapL TB1 DB1 f = f := by decide +kernel
theorem rank1 : rankK 1 TB1 DB1 = true := by decide +kernel
theorem cv1 : CV1 < 2 ^ (25 * 2280) ∧ ∀ t < 2280, laneW 25 CV1 t < 2 ^ 24 := by decide +kernel
theorem cs1 : CS1 < 2 ^ (25 * 120) ∧ ∀ t < 120, laneW 25 CS1 t < 2 ^ 24 := by decide +kernel

theorem pass1_0 : passRange (passT TT1 0 2280 CV1 120 CS1) 0 512 = true := by quickRfl
theorem pass1_1 : passRange (passT TT1 0 2280 CV1 120 CS1) 512 512 = true := by quickRfl
theorem pass1_2 : passRange (passT TT1 0 2280 CV1 120 CS1) 1024 512 = true := by quickRfl
theorem pass1_3 : passRange (passT TT1 0 2280 CV1 120 CS1) 1536 512 = true := by quickRfl
theorem pass1_4 : passRange (passT TT1 0 2280 CV1 120 CS1) 2048 512 = true := by quickRfl
theorem pass1_5 : passRange (passT TT1 0 2280 CV1 120 CS1) 2560 512 = true := by quickRfl
theorem pass1_6 : passRange (passT TT1 0 2280 CV1 120 CS1) 3072 512 = true := by quickRfl
theorem pass1_7 : passRange (passT TT1 0 2280 CV1 120 CS1) 3584 512 = true := by quickRfl

end CertificateChecks.MonsterExist.ELevel

end

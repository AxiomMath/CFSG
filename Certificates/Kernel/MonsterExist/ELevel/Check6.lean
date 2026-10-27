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

theorem perm6 : PermArr (cosetArr 6) = true := by decide +kernel
theorem aut6 : AutArr (cosetArr 6) := by decide +kernel
theorem basis6 : BasisOK 6 TB6 DB6 := by unfold BasisOK; decide +kernel
theorem tt6 : ttOK TB6 DB6 FB6 TT6 = true := by quickRfl
theorem xw6 : packP (wP 6) = 0 := by decide +kernel
theorem sw6 : synL FB6 0 = 0 := by decide +kernel
theorem elim6 : elimGo (fun x => x ^^^ kapL TB6 DB6 x) 24 [] [] = (PIV6, FB6) := by decide +kernel
theorem fb6 : ∀ f ∈ FB6, kapL TB6 DB6 f = f := by decide +kernel
theorem rank6 : rankK 6 TB6 DB6 = true := by decide +kernel

theorem pass6_0 : passRange (passT TT6 0 0 0 0 0) 0 512 = true := by quickRfl
theorem pass6_1 : passRange (passT TT6 0 0 0 0 0) 512 512 = true := by quickRfl
theorem pass6_2 : passRange (passT TT6 0 0 0 0 0) 1024 512 = true := by quickRfl
theorem pass6_3 : passRange (passT TT6 0 0 0 0 0) 1536 512 = true := by quickRfl
theorem pass6_4 : passRange (passT TT6 0 0 0 0 0) 2048 512 = true := by quickRfl
theorem pass6_5 : passRange (passT TT6 0 0 0 0 0) 2560 512 = true := by quickRfl
theorem pass6_6 : passRange (passT TT6 0 0 0 0 0) 3072 512 = true := by quickRfl
theorem pass6_7 : passRange (passT TT6 0 0 0 0 0) 3584 512 = true := by quickRfl

end CertificateChecks.MonsterExist.ELevel

end

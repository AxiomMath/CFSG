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

theorem inner1_4 : innerRange TB1 DB1 PIV1 0 120 CS1 CV1 1140 285 = true := by quickRfl
theorem inner1_5 : innerRange TB1 DB1 PIV1 0 120 CS1 CV1 1425 285 = true := by quickRfl
theorem inner1_6 : innerRange TB1 DB1 PIV1 0 120 CS1 CV1 1710 285 = true := by quickRfl
theorem inner1_7 : innerRange TB1 DB1 PIV1 0 120 CS1 CV1 1995 285 = true := by quickRfl

end CertificateChecks.MonsterExist.ELevel

end

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

theorem perm2 : PermArr (cosetArr 2) = true := by decide +kernel
theorem aut2 : AutArr (cosetArr 2) := by decide +kernel
theorem basis2 : BasisOK 2 TB2 DB2 := by unfold BasisOK; decide +kernel
theorem tt2 : ttOK TB2 DB2 FB2 TT2 = true := by quickRfl
theorem xw2 : packP (wP 2) = 63 := by decide +kernel
theorem sw2 : synL FB2 63 = 0 := by decide +kernel
theorem elim2 : elimGo (fun x => x ^^^ kapL TB2 DB2 x) 24 [] [] = (PIV2, FB2) := by decide +kernel
theorem fb2 : ∀ f ∈ FB2, kapL TB2 DB2 f = f := by decide +kernel
theorem rank2 : rankK 2 TB2 DB2 = true := by decide +kernel
theorem cv2 : CV2 < 2 ^ (25 * 264) ∧ ∀ t < 264, laneW 25 CV2 t < 2 ^ 24 := by decide +kernel
theorem cs2 : CS2 < 2 ^ (25 * 264) ∧ ∀ t < 264, laneW 25 CS2 t < 2 ^ 24 := by decide +kernel

theorem pass2_0 : passRange (passT TT2 0 264 CV2 264 CS2) 0 512 = true := by quickRfl
theorem pass2_1 : passRange (passT TT2 0 264 CV2 264 CS2) 512 512 = true := by quickRfl
theorem pass2_2 : passRange (passT TT2 0 264 CV2 264 CS2) 1024 512 = true := by quickRfl
theorem pass2_3 : passRange (passT TT2 0 264 CV2 264 CS2) 1536 512 = true := by quickRfl
theorem pass2_4 : passRange (passT TT2 0 264 CV2 264 CS2) 2048 512 = true := by quickRfl
theorem pass2_5 : passRange (passT TT2 0 264 CV2 264 CS2) 2560 512 = true := by quickRfl
theorem pass2_6 : passRange (passT TT2 0 264 CV2 264 CS2) 3072 512 = true := by quickRfl
theorem pass2_7 : passRange (passT TT2 0 264 CV2 264 CS2) 3584 512 = true := by quickRfl

theorem inner2_0 : innerRange TB2 DB2 PIV2 63 264 CS2 CV2 0 66 = true := by quickRfl
theorem inner2_1 : innerRange TB2 DB2 PIV2 63 264 CS2 CV2 66 66 = true := by quickRfl
theorem inner2_2 : innerRange TB2 DB2 PIV2 63 264 CS2 CV2 132 66 = true := by quickRfl
theorem inner2_3 : innerRange TB2 DB2 PIV2 63 264 CS2 CV2 198 66 = true := by quickRfl

end CertificateChecks.MonsterExist.ELevel

end

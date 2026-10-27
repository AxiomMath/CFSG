module

public import Certificates.Kernel.Misc.RuFourth.Bind
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuFourth

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuFourth

theorem perm0 : permOK 16240 14 16383 (16240 * 14) (RK 0) (RIK 0) = true := by quickRfl
theorem perm1 : permOK 16240 14 16383 (16240 * 14) (RK 1) (RIK 1) = true := by quickRfl
theorem perm2 : permOK 16240 14 16383 (16240 * 14) (RK 2) (RIK 2) = true := by quickRfl

theorem lettersOK : letters3 (intsK RuFST.chars) = true := by quickRfl

theorem zMoves : zOK RK RIK (intsK RuFST.chars) 0 = true := by quickRfl

theorem w1OK : oneP RK RIK (intsK RuFST.chars) (wordFrom RK RIK [-3, 2] idP) 320 0 = true := by
  quickRfl

theorem c1OK : Nat.beq (wordFrom RK RIK [-2, -1, -3, -1, -3, -1, 3] idP) C1 = true := by quickRfl

theorem x2OK : Nat.beq (wordFrom RK RIK [-2, -1, -3, -1, -3, -1, 3] C1) X2 = true := by quickRfl

theorem w2X : oneP RK RIK (intsK RuFST.chars) X2 48 0 = true := by quickRfl

theorem w2X_neg : (!oneP RK RIK (intsK RuFST.chars) X2 320 0) = true := by quickRfl

end CertificateChecks.KernelMisc.RuFourth

end

module

public import Certificates.Kernel.Sporadic.M12Alt.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.M12Alt

open CFSG.KS CFSG.KS.MEnum CFSG.KS.M11

theorem base : mBase 12 4 [0, 1, 2, 3, 4] [12, 11, 10, 9, 8] 12 tA tB W = true := by quickRfl

theorem c0 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 0 3 11 Rs) (CS.getD 0 0) = true := by
  quickRfl

theorem c1 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 1 3 11 Rs) (CS.getD 1 0) = true := by
  quickRfl

theorem c2 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 2 3 11 Rs) (CS.getD 2 0) = true := by
  quickRfl

theorem c3 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 3 3 11 Rs) (CS.getD 3 0) = true := by
  quickRfl

theorem c4 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 4 3 11 Rs) (CS.getD 4 0) = true := by
  quickRfl

theorem c5 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 5 3 11 Rs) (CS.getD 5 0) = true := by
  quickRfl

theorem c6 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 6 3 11 Rs) (CS.getD 6 0) = true := by
  quickRfl

theorem c7 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 7 3 11 Rs) (CS.getD 7 0) = true := by
  quickRfl

theorem c8 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 8 3 11 Rs) (CS.getD 8 0) = true := by
  quickRfl

theorem c9 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 9 3 11 Rs) (CS.getD 9 0) = true := by
  quickRfl

theorem c10 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 10 3 11 Rs) (CS.getD 10 0) = true := by
  quickRfl

theorem c11 : Nat.beq (mCntZ 12 4 [0, 1, 2, 3, 4] 12 tA tB W 1 11 3 11 Rs) (CS.getD 11 0) = true := by
  quickRfl

theorem oA : Nat.beq (ordC 12 4 15 (packL 4 tA)) 2 = true := by quickRfl

theorem oB : Nat.beq (ordC 12 4 15 (packL 4 tB)) 3 = true := by quickRfl

theorem pAB : pairOKG 12 4 15 11 6 (packL 4 tA) (pinvS 12 4 15 (packL 4 tA))
    (packL 4 tB) (pinvS 12 4 15 (packL 4 tB)) = true := by quickRfl

theorem cls : allC (clsOneR 12 4 tA tB 2 1000) CL = true := by quickRfl

theorem disj : clsDisj 12 4 CL = true := by quickRfl

end CertificateChecks.KernelSpor.M12Alt

end

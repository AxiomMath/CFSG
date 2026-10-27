module

public import Certificates.Kernel.Sporadic.M22Alt.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSpor.M22Alt

open CFSG.KS CFSG.KS.MEnum CFSG.KS.M11

theorem base : mBase 22 5 [0, 1, 2, 3, 4] [22, 21, 20, 16, 3] 13 tA tB W = true := by quickRfl

theorem c0 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 0 4 11 Rs) (CS.getD 0 0) = true := by
  quickRfl

theorem c1 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 1 4 11 Rs) (CS.getD 1 0) = true := by
  quickRfl

theorem c2 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 2 4 11 Rs) (CS.getD 2 0) = true := by
  quickRfl

theorem c3 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 3 4 11 Rs) (CS.getD 3 0) = true := by
  quickRfl

theorem c4 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 4 4 11 Rs) (CS.getD 4 0) = true := by
  quickRfl

theorem c5 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 5 4 11 Rs) (CS.getD 5 0) = true := by
  quickRfl

theorem c6 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 6 4 11 Rs) (CS.getD 6 0) = true := by
  quickRfl

theorem c7 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 7 4 11 Rs) (CS.getD 7 0) = true := by
  quickRfl

theorem c8 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 8 4 11 Rs) (CS.getD 8 0) = true := by
  quickRfl

theorem c9 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 9 4 11 Rs) (CS.getD 9 0) = true := by
  quickRfl

theorem c10 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 10 4 11 Rs) (CS.getD 10 0) = true := by
  quickRfl

theorem c11 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 11 4 11 Rs) (CS.getD 11 0) = true := by
  quickRfl

theorem c12 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 12 4 11 Rs) (CS.getD 12 0) = true := by
  quickRfl

theorem c13 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 13 4 11 Rs) (CS.getD 13 0) = true := by
  quickRfl

theorem c14 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 14 4 11 Rs) (CS.getD 14 0) = true := by
  quickRfl

theorem c15 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 15 4 11 Rs) (CS.getD 15 0) = true := by
  quickRfl

theorem c16 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 16 4 11 Rs) (CS.getD 16 0) = true := by
  quickRfl

theorem c17 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 17 4 11 Rs) (CS.getD 17 0) = true := by
  quickRfl

theorem c18 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 18 4 11 Rs) (CS.getD 18 0) = true := by
  quickRfl

theorem c19 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 19 4 11 Rs) (CS.getD 19 0) = true := by
  quickRfl

theorem c20 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 20 4 11 Rs) (CS.getD 20 0) = true := by
  quickRfl

theorem c21 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 21 4 11 Rs) (CS.getD 21 0) = true := by
  quickRfl

theorem c22 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 22 4 11 Rs) (CS.getD 22 0) = true := by
  quickRfl

theorem c23 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 23 4 11 Rs) (CS.getD 23 0) = true := by
  quickRfl

theorem c24 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 24 4 11 Rs) (CS.getD 24 0) = true := by
  quickRfl

theorem c25 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 25 4 11 Rs) (CS.getD 25 0) = true := by
  quickRfl

theorem c26 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 26 4 11 Rs) (CS.getD 26 0) = true := by
  quickRfl

theorem c27 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 27 4 11 Rs) (CS.getD 27 0) = true := by
  quickRfl

theorem c28 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 28 4 11 Rs) (CS.getD 28 0) = true := by
  quickRfl

theorem c29 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 29 4 11 Rs) (CS.getD 29 0) = true := by
  quickRfl

theorem c30 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 30 4 11 Rs) (CS.getD 30 0) = true := by
  quickRfl

theorem c31 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 31 4 11 Rs) (CS.getD 31 0) = true := by
  quickRfl

theorem c32 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 32 4 11 Rs) (CS.getD 32 0) = true := by
  quickRfl

theorem c33 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 33 4 11 Rs) (CS.getD 33 0) = true := by
  quickRfl

theorem c34 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 34 4 11 Rs) (CS.getD 34 0) = true := by
  quickRfl

theorem c35 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 35 4 11 Rs) (CS.getD 35 0) = true := by
  quickRfl

theorem c36 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 36 4 11 Rs) (CS.getD 36 0) = true := by
  quickRfl

theorem c37 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 37 4 11 Rs) (CS.getD 37 0) = true := by
  quickRfl

theorem c38 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 38 4 11 Rs) (CS.getD 38 0) = true := by
  quickRfl

theorem c39 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 39 4 11 Rs) (CS.getD 39 0) = true := by
  quickRfl

theorem c40 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 40 4 11 Rs) (CS.getD 40 0) = true := by
  quickRfl

theorem c41 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 41 4 11 Rs) (CS.getD 41 0) = true := by
  quickRfl

theorem c42 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 42 4 11 Rs) (CS.getD 42 0) = true := by
  quickRfl

theorem c43 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 43 4 11 Rs) (CS.getD 43 0) = true := by
  quickRfl

theorem c44 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 44 4 11 Rs) (CS.getD 44 0) = true := by
  quickRfl

theorem c45 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 45 4 11 Rs) (CS.getD 45 0) = true := by
  quickRfl

theorem c46 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 46 4 11 Rs) (CS.getD 46 0) = true := by
  quickRfl

theorem c47 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 47 4 11 Rs) (CS.getD 47 0) = true := by
  quickRfl

theorem c48 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 48 4 11 Rs) (CS.getD 48 0) = true := by
  quickRfl

theorem c49 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 49 4 11 Rs) (CS.getD 49 0) = true := by
  quickRfl

theorem c50 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 50 4 11 Rs) (CS.getD 50 0) = true := by
  quickRfl

theorem c51 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 51 4 11 Rs) (CS.getD 51 0) = true := by
  quickRfl

theorem c52 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 52 4 11 Rs) (CS.getD 52 0) = true := by
  quickRfl

theorem c53 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 53 4 11 Rs) (CS.getD 53 0) = true := by
  quickRfl

theorem c54 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 54 4 11 Rs) (CS.getD 54 0) = true := by
  quickRfl

theorem c55 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 55 4 11 Rs) (CS.getD 55 0) = true := by
  quickRfl

theorem c56 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 56 4 11 Rs) (CS.getD 56 0) = true := by
  quickRfl

theorem c57 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 57 4 11 Rs) (CS.getD 57 0) = true := by
  quickRfl

theorem c58 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 58 4 11 Rs) (CS.getD 58 0) = true := by
  quickRfl

theorem c59 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 59 4 11 Rs) (CS.getD 59 0) = true := by
  quickRfl

theorem c60 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 60 4 11 Rs) (CS.getD 60 0) = true := by
  quickRfl

theorem c61 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 61 4 11 Rs) (CS.getD 61 0) = true := by
  quickRfl

theorem c62 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 62 4 11 Rs) (CS.getD 62 0) = true := by
  quickRfl

theorem c63 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 63 4 11 Rs) (CS.getD 63 0) = true := by
  quickRfl

theorem c64 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 64 4 11 Rs) (CS.getD 64 0) = true := by
  quickRfl

theorem c65 : Nat.beq (mCntZ 22 5 [0, 1, 2, 3, 4] 13 tA tB W 3 65 4 11 Rs) (CS.getD 65 0) = true := by
  quickRfl

theorem oA : Nat.beq (ordC 22 5 31 (packL 5 tA)) 2 = true := by quickRfl

theorem oB : Nat.beq (ordC 22 5 31 (packL 5 tB)) 4 = true := by quickRfl

theorem pAB : pairOKG 22 5 31 11 6 (packL 5 tA) (pinvS 22 5 31 (packL 5 tA))
    (packL 5 tB) (pinvS 22 5 31 (packL 5 tB)) = true := by quickRfl

theorem cls : allC (clsOneR 22 5 tA tB 2 2000) CL = true := by quickRfl

theorem disj : clsDisj 22 5 CL = true := by quickRfl

end CertificateChecks.KernelSpor.M22Alt

end

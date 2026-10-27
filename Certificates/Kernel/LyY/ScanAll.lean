module

public import Certificates.Kernel.LyY.ScanA
public import Certificates.Kernel.LyY.ScanB
public import Certificates.Kernel.LyY.ScanC
public import Certificates.Kernel.LyY.ScanD
public import Certificates.Kernel.LyY.ScanE
public import Certificates.Kernel.LyY.ScanF
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Child3 CFSG.KC.J2Enum CFSG.KC.LyY CFSG.KC.Co3Bfs
open CFSG.Sporadic.Recognition.LyonsSims

theorem fC_all : ∀ k < 54, fC k = true := by
  intro k hk
  interval_cases k
  exacts [fC0, fC1, fC2, fC3, fC4, fC5, fC6, fC7, fC8, fC9, fC10, fC11, fC12, fC13, fC14, fC15,
    fC16, fC17, fC18, fC19, fC20, fC21, fC22, fC23, fC24, fC25, fC26, fC27, fC28, fC29, fC30, fC31,
    fC32, fC33, fC34, fC35, fC36, fC37, fC38, fC39, fC40, fC41, fC42, fC43, fC44, fC45, fC46, fC47,
    fC48, fC49, fC50, fC51, fC52, fC53]

theorem fE_all : ∀ a < 1080, fE a = true :=
  cover_of_blocks (by norm_num) (by norm_num : 1080 ≤ 20 * 54) fC_all

theorem k_tot : bAnd(Nat.beq (fld20 (sumF 1080 (lget E)) 0) 288,
    Nat.beq (fld20 (sumF 1080 (lget E)) 1) 2511) = true := by
  quickRfl

end CertificateChecks.KernelLyY

end

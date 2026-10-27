module

public import Certificates.Kernel.Sporadic.M11.Data
public import Certificates.Kernel.Sporadic.M11Alt.Data
public import Certificates.Data.Kernel.Spor.M11Class
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.M11Alt

open CFSG.KS CFSG.KS.M11 CFSG.KS.M11Class CertificateChecks.KernelSpor.M11

@[expose] def tA : List Nat := [0, 9, 2, 10, 6, 5, 4, 8, 7, 1, 3]

@[expose] def tB : List Nat := [3, 4, 7, 2, 5, 8, 6, 0, 1, 9, 10]

@[expose] def W : List (List Int) :=
  [[1], [2], [-4, -3, 4, 3, 4], [5, -4, -3, -5, 4], [-5, -3, -5, -6, -4, -4, -5, 6, 5, 4],
    [-5, -3, -5, -3, -4, -7, 3, -4]]

@[expose] def XL : List (Nat × Nat) :=
  X0 ++ X1 ++ X2 ++ X3 ++ X4 ++ X5 ++ X6 ++ X7 ++ X8 ++ X9 ++ X10

theorem base : m11Base tA tB W = true := by quickRfl

theorem colX : Nat.beq (m11Col tA tB W 1) (packPairs XL) = true := by quickRfl

theorem colY : Nat.beq (m11Col tA tB W 3) (packPairs Y) = true := by quickRfl

theorem cls : classRowOK (packL 4 tA) (pinvS 11 4 15 (packL 4 tA)) (packL 4 tB)
    (pinvS 11 4 15 (packL 4 tB)) R Ri Bl P Lb S SY XL Y 1000 = true := by quickRfl

theorem row : Nat.beq (rowCnt R Ri Y) 96 = true := by quickRfl

end CertificateChecks.KernelSpor.M11Alt

end

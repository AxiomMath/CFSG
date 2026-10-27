module

public import Certificates.Kernel.Q16Sp6.Data
public import Certificates.Kernel.Sporadic.Co3.Sp36
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.Misc.ArrEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ16Sp6

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Q16BK CFSG.KC.Misc.ArrEnum

@[expose] def words : List (List Nat) :=
  [[0], [1], [2], [3], [4], [5], [9, 7], [11, 7], [19, 15]]

@[expose] noncomputable def CS.SK : List Nat := (List.range 512).map CS.SKT

theorem nums : (Nat.beq CS.ng 9 && Nat.beq CS.N 512) = true := by quickRfl

theorem gens : allN 9 (fun k => Nat.beq (CS.G k)
    (posWordK 36 6 CertificateChecks.KernelSpor.Co3Sp36.S (words.getD k []))) = true := by
  quickRfl

theorem perm : allN 9 (fun k => permB 36 6 (CS.G k)) = true := by quickRfl

theorem keys : keysSK 36 6 [4, 0, 2] CS.N CS.T CS.SK = true := by quickRfl

theorem q16 : q16BK 36 6 [4, 0, 2] CS.N CS.T CS.nR CS.RI CS.C CS.W = true := by quickRfl

end CertificateChecks.KernelQ16Sp6

end

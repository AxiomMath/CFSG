module

public import Certificates.Kernel.NT44.Pack
public meta import Certificates.Data.NT44Model.Inputs
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 200

public section

namespace CertificateChecks.KernelNT44

@[expose] def nt44WkD : List (List Int) :=
  (CFSG.GH74.GLS.NT44.PermutationNative.wk ()).toList.drop 2

meta def skCM : Array (Array Nat) := CFSG.GH74.GLS.NT44.PermutationNative.sk ()

meta def bkCM : Array Nat := CFSG.GH74.GLS.NT44.PermutationNative.bk ()

end CertificateChecks.KernelNT44

end

#ks_rawchain CertificateChecks.KernelNT44.CK 448 9 448 CertificateChecks.KernelNT44.skCM
  CertificateChecks.KernelNT44.bkCM 2 CertificateChecks.KernelNT44.nt44WkD

public section

namespace CertificateChecks.KernelNT44.CK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem bS : allN 7 (fun j => Nat.beq (S j) (CertificateChecks.KernelNT44.nt44SK j)) = true := by
  quickRfl

theorem perm : allN 7 (fun j => permOK 448 9 (mask 9) (448 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 4, (CFSG.GH74.GLS.NT44.PermutationNative.bk ())[t]! = pg 9 (mask 9) BP t := by
  decide +kernel

theorem orbProd : ((List.range 4).map fun i => rcnt (LR i)).prod = 322560 := by decide +kernel

theorem hNS : 448 ≤ NS * 448 := by decide +kernel

end CertificateChecks.KernelNT44.CK

end

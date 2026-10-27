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

@[expose] def nt44WpD : List (List Int) :=
  (CFSG.GH74.GLS.NT44.PermutationNative.wp ()).toList.drop 9

meta def spCM : Array (Array Nat) := CFSG.GH74.GLS.NT44.PermutationNative.sp ()

meta def bpCM : Array Nat := CFSG.GH74.GLS.NT44.PermutationNative.bp ()

end CertificateChecks.KernelNT44

end

#ks_rawchain CertificateChecks.KernelNT44.CP 448 9 448 CertificateChecks.KernelNT44.spCM
  CertificateChecks.KernelNT44.bpCM 9 CertificateChecks.KernelNT44.nt44WpD

public section

namespace CertificateChecks.KernelNT44.CP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem bS : allN 10 (fun j => Nat.beq (S j) (CertificateChecks.KernelNT44.nt44SP j)) = true := by
  quickRfl

theorem perm : allN 10 (fun j => permOK 448 9 (mask 9) (448 * 9) (S j) (SI j)) = true := by
  quickRfl

theorem bget : ∀ t < 3, (CFSG.GH74.GLS.NT44.PermutationNative.bp ())[t]! = pg 9 (mask 9) BP t := by
  decide +kernel

theorem orbProd : ((List.range 3).map fun i => rcnt (LR i)).prod = 1024 := by decide +kernel

theorem hNS : 448 ≤ NS * 448 := by decide +kernel

end CertificateChecks.KernelNT44.CP

end

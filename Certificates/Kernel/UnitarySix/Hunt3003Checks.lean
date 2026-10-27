module

public import Certificates.Kernel.UnitarySix.M22Chunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.U6 CFSG.EvenSmallLie.UnitarySix.Hunt
open CFSG.KLie.CT (fget sumN)

theorem permC : allN 11 (fun j => permOK 22 5 (mask 5) (22 * 5) (M22C.S j) (M22C.SI j)) = true := by
  quickRfl

theorem kRoot8 : rootK 256 key8 keys8 = true := by quickRfl
theorem kRoot0 : rootK 256 key0 keys0 = true := by quickRfl
theorem kRootY : rootK 512 keyY keysY = true := by quickRfl

theorem kDig : ∀ k ∈ [key8, key0, keyY], ∀ i < 22, fget (unkey k) i 5 < 22 := by decide +kernel
theorem kKeys : ∀ k ∈ keys8 ++ keys0 ++ keysY, k < 2 ^ 110 ∧ ∀ i < 22, fget (unkey k) i 5 < 22 := by
  decide +kernel
theorem kSorted : keys8.Pairwise (· < ·) ∧ keys0.Pairwise (· < ·) ∧ keysY.Pairwise (· < ·) := by
  decide +kernel

theorem kTot : (List.range 6).map (fun k => fget (sumN 22 fun a => VN.getD a 0) k 20) =
    [0, 1716, 1155, 1344, 320, 384] := by
  decide +kernel

end CertificateChecks.KernelU6

end

module

public import Certificates.Kernel.UnitarySix.Sec3.E3600Chk
public import Certificates.Kernel.UnitarySix.Letters
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.RankThree.Native CFSG.KC.U6

@[expose] noncomputable def packC (C : Array ℕ) : ℕ :=
  (List.range 36).foldr (fun j acc => C[j]! + 4 * acc) 0

theorem hQ : qmCodes = decA (packC qmCodes) 2 36 := by decide +kernel
theorem hQI : qimCodes = decA (packC qimCodes) 2 36 := by decide +kernel
theorem hCodes : ∀ k < 18, yamCodes[k]! = decA (packC yamCodes[k]!) 2 36 := by decide +kernel

theorem kTab0 : ∀ k < 6,
    tabK (packC qmCodes) (packC qimCodes) (packC yamCodes[k]!) U.UP U.POS (sec3G k) = true := by
  decide +kernel
theorem kTab1 : ∀ k < 6, tabK (packC qmCodes) (packC qimCodes) (packC yamCodes[k + 6]!) U.UP U.POS
    (sec3G (k + 6)) = true := by
  decide +kernel
theorem kTab2 : ∀ k < 6, tabK (packC qmCodes) (packC qimCodes) (packC yamCodes[k + 12]!) U.UP
    U.POS (sec3G (k + 12)) = true := by
  decide +kernel

theorem kTab : ∀ k < 18,
    tabK (packC qmCodes) (packC qimCodes) (packC yamCodes[k]!) U.UP U.POS (sec3G k) = true := by
  intro k hk
  rcases Nat.lt_or_ge k 6 with h | h
  · exact kTab0 k h
  rcases Nat.lt_or_ge k 12 with h' | h'
  · have := kTab1 (k - 6) (by omega)
    rwa [Nat.sub_add_cancel h] at this
  · have := kTab2 (k - 12) (by omega)
    rwa [Nat.sub_add_cancel h'] at this

end CertificateChecks.KernelU6.Sec3

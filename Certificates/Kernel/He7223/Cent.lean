module

public import Certificates.Data.Kernel.Misc.OrbPath
public import Certificates.Kernel.He7223.CentData
public import Certificates.Kernel.He7223.Pts
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHe7223

open CFSG.KLie.CT CFSG.KC.WordPts CFSG.KC.OrbPath CertificateChecks.KernelLC.HeFix
open CFSG.KS CFSG.KS.Prim
open CFSG.KC.Enum (permOK pidn)

@[expose] noncomputable def HC (j : Nat) : Nat := [PC5, PC10, PSG].getD j 0

@[expose] noncomputable def HCI (j : Nat) : Nat := [PC5I, PC10I, PSGI].getD j 0

@[expose] noncomputable def T5 : List (List Int) := [EB.getD 1 [], EB.getD 2 [], EB.getD 3 []]

@[expose] noncomputable def T7 : List (List Int) := [QB.getD 1 [], QB.getD 2 []]

@[expose] noncomputable def C5 (c : Nat) : Nat := O5.getD c 0

@[expose] noncomputable def C7 (c : Nat) : Nat := O7.getD c 0

@[expose] noncomputable def rec5 (N k : Nat) : Bool := orbRecK 8330 14 LU LUI HC HCI 16 0 T5 74 6 C5 N k

@[expose] noncomputable def rec7 (N k : Nat) : Bool := orbRecK 8330 14 LU LUI HC HCI 16 0 T7 60 6 C7 N k

theorem ch7223kH5 : wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (gw 9) PC5 = true := by
  quickRfl

theorem ch7223kH10 : wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (gw 10) PC10 = true := by
  quickRfl

theorem ch7223kHS : wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (gw 7) PSG = true := by
  quickRfl

theorem ch7223kHI : allN 3 (fun j => permOK 8330 14 (mask 14) (8330 * 14) (HC j) (HCI j)) = true := by
  quickRfl

theorem ch7223o5 : ∀ k < 672, rec5 672 k = true := by kc_cover 64

theorem ch7223o7 : ∀ k < 2688, rec7 2688 k = true := by kc_cover 64

end CertificateChecks.KernelHe7223

end

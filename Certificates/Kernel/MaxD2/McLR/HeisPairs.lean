module

public import Certificates.Kernel.MaxD2.McLR.Enum
public import Certificates.Kernel.MaxD2.McLR.Data
public import Certificates.Kernel.MaxD2.McLR.HeisData
public import Certificates.Data.Kernel.MaxD2.Pair
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

@[expose] noncomputable def pairsK (c : Nat) : Bool :=
  allN 21 (fun d => strictB (Nat.add (Nat.mul 21 c) d) (fun q =>
    pairK 275 9 2 18 NE.cnt (r32 PT) NE.T FS KS REP REPI RB2 H2 q (r32 PI q) (r32 PJ q)))

theorem k_np2 : Nat.beq (r32 MISC 1) 273 = true := by quickRfl
theorem k_pair0 : pairsK 0 = true := by quickRfl
theorem k_pair1 : pairsK 1 = true := by quickRfl
theorem k_pair2 : pairsK 2 = true := by quickRfl
theorem k_pair3 : pairsK 3 = true := by quickRfl
theorem k_pair4 : pairsK 4 = true := by quickRfl
theorem k_pair5 : pairsK 5 = true := by quickRfl
theorem k_pair6 : pairsK 6 = true := by quickRfl
theorem k_pair7 : pairsK 7 = true := by quickRfl
theorem k_pair8 : pairsK 8 = true := by quickRfl
theorem k_pair9 : pairsK 9 = true := by quickRfl
theorem k_pair10 : pairsK 10 = true := by quickRfl
theorem k_pair11 : pairsK 11 = true := by quickRfl
theorem k_pair12 : pairsK 12 = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLR

end

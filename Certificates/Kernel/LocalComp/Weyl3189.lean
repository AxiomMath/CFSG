module

public import Certificates.Kernel.LocalComp.E8Tables
public import CFSG.Certificates.Kernel.LocalCompD8Sound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylD8Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases
public import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3189

open CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight.Weyl

theorem kPairs : bindPairs E8.DP dPairs = true := by quickRfl
theorem k1 : d1K E8.ST = true := by quickRfl
theorem k2 : d2K E8.RT E8.ST = true := by quickRfl
@[expose] noncomputable def k3F (p : Nat) : Bool := d3At E8.RT E8.ST E8.DP p

#kc_each_unfold k3F 0 28 as CertificateChecks.KernelLC.W3189.k3_

#kc_forall_chunks k3K (fun p => d3At E8.RT E8.ST E8.DP p = true) 28
  CertificateChecks.KernelLC.W3189.k3_ 1

theorem k3 : ∀ p < 28, d3At E8.RT E8.ST E8.DP p = true := k3K
theorem k5 : d5K E8.RK E8.RT E8.PT E8.DP = true := by quickRfl
theorem kInv : CFSG.KC.Enum.allN 112 (fun r => CFSG.KC.Enum.permOK 240 8 255 1920 (E8.RT r) (E8.RT r)) =
    true := by quickRfl

theorem neg_inv : notB' (CFSG.KC.Enum.allN 112 (fun r => CFSG.KC.Enum.permOK 240 8 255 1920
    (Nat.xor (E8.RT r) 1) (Nat.xor (E8.RT r) 1))) = true := by quickRfl

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3189 : dCheck = true := by
  rw [dCheck_eq]
  exact d8_sound E8.bind E8.sorted E8.hrt E8.hst kInv kPairs k1 k2 k3 k5

end CertificateChecks.KernelLC.W3189

end

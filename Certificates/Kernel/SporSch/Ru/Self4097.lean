module

public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuSelfInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSelf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.QuasithinUnique.Vol2Native.L239.RuPairs CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def imgSj (k : Nat) : Bool :=
  strictB (Nat.div k 6) (fun j => strictB (Nat.mod k 6) (fun i =>
    sortImgK 4060 12 (SG j) (ruCBlockList i) (ruCBlockList (ruSBlockArr j)[i]!)))

end CertificateChecks.KernelSporSch.RuSelf

#kss_each CertificateChecks.KernelSporSch.RuSelf.IS CertificateChecks.KernelSporSch.RuSelf.imgSj 24

namespace CertificateChecks.KernelSporSch.RuSelf

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.QuasithinUnique.Vol2Native.L239.RuPairs CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuCe

theorem pbS : allN 4 (fun j => allN 6 (fun i => Nat.blt (ruSBlockArr j)[i]! 6)) = true := by
  quickRfl

theorem is_h {j i : Nat} (hj : j < 4) (hi : i < 6) :
    sortImgK 4060 12 (SG j) (ruCBlockList i) (ruCBlockList (ruSBlockArr j)[i]!) = true := by
  have hk : 6 * j + i < 24 := by omega
  have h := IS.all (6 * j + i) hk
  unfold imgSj at h
  rw [sb_eq, sb_eq] at h
  have e1 : Nat.div (6 * j + i) 6 = j := by
    change (6 * j + i) / 6 = j
    omega
  have e2 : Nat.mod (6 * j + i) 6 = i := by
    change (6 * j + i) % 6 = i
    omega
  rw [e1, e2] at h
  exact h

theorem facts : (∀ j < 4, ∀ i < 6, imgSorted ruSGensA[j]! (ruCBlockList i) =
      ruCBlockList (ruSBlockArr j)[i]!) ∧ (∀ j < 4, ∀ i < 6, (ruSBlockArr j)[i]! < 6) := by
  refine ⟨fun j hj i hi => ?_, fun j hj i hi => by
    simpa [Nat.blt_eq] using allN_spec (allN_spec pbS j hj) i hi⟩
  rw [sg_eq hj]
  exact imgK_sound (is_h hj hi)

end CertificateChecks.KernelSporSch.RuSelf

end

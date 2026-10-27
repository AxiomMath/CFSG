module

public import Certificates.Kernel.OmegaEight.Chain3850
import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelO8.C3850

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.KC.Enum
  CFSG.KS CFSG.KS.Raw CFSG.Certificates.Native CertificateChecks.KernelO8.Chain3850

theorem bindsP : Binds 64 7 CP.S 16 6 CP.BP (strong .plus) (chainBase .plus).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, ?_, rfl, ?_⟩
  · decide +kernel
  · decide +kernel

theorem bindsM : Binds 64 7 CM.S 14 6 CM.BP (strong .minus) (chainBase .minus).toArray := by
  refine ⟨by norm_num, by norm_num, by norm_num, by decide +kernel, ?_, rfl, ?_⟩
  · decide +kernel
  · decide +kernel

theorem wordsP :
    chainWords .plus = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 16 extraWordsPlus := by
  decide +kernel

theorem wordsM :
    chainWords .minus = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 7 14 extraWordsMinus := by
  decide +kernel

theorem chain_plus : nsChainCheck .plus = true := by
  have raw := rawChainK_sound (NS := 1) (CH := 64) (chunks := 1) bindsP CP.head CP.hl
    (by norm_num) CP.hs
  have orb := rawOrbitSizesK_sound bindsP permP CP.hl
  unfold nsChainCheck
  rw [wordsP, raw, orb, Bool.true_and]
  decide +kernel

theorem chain_minus : nsChainCheck .minus = true := by
  have raw := rawChainK_sound (NS := 1) (CH := 64) (chunks := 1) bindsM CM.head CM.hl
    (by norm_num) CM.hs
  have orb := rawOrbitSizesK_sound bindsM permM CM.hl
  unfold nsChainCheck
  rw [wordsM, raw, orb, Bool.true_and]
  decide +kernel

end CertificateChecks.KernelO8.C3850

end

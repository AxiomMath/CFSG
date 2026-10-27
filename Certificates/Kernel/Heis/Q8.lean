module

public import Certificates.Kernel.Misc.ArgChars
public import Certificates.Data.Kernel.HeisWordsK
public import Certificates.Data.Kernel.OuterN
public import CFSG.LieType.SeitzGeneration.OuterSmallData8

public section

set_option maxRecDepth 1000000

#kc_arg_chars CertificateChecks.KernelHeis.W8 CFSG.LieType.SeitzGeneration.HeisSmall.words2_8

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN

theorem heis8_k : fk8.heisN 8 8 rawGens8 words1_8 (decodeL W8.chars) = true := by
  decide +kernel

theorem heis8_neg_gen :
    fk8.heisN 8 8 ([1, 0, 0, 0, 8, 0, 0, 0, 8] :: rawGens8.tail) words1_8 (decodeL W8.chars) =
      false := by
  decide +kernel

theorem heis8_neg_cover :
    fk8.heisN 8 8 rawGens8 words1_8 (decodeL W8.chars).dropLast = false := by
  decide +kernel

theorem outer8_k : fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars) outerRaw8 = true := by
  decide +kernel

theorem outer8_neg_cover :
    fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars).dropLast outerRaw8 = false := by
  decide +kernel

theorem outer8_neg_gen :
    fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars)
      (outerRaw8.map fun r => (r.1, [1, 0, 0, 0, 8, 0, 0, 0, 8] :: r.2.1.tail, r.2.2)) =
      false := by
  decide +kernel

theorem outer8_neg_line :
    fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars)
      (match outerRaw8 with
        | r :: s :: t => (s.1, r.2) :: (r.1, s.2) :: t
        | t => t) = false := by
  decide +kernel

theorem outer8_neg_letters :
    fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars)
      (outerRaw8.map fun r => (r.1, r.2.1, r.2.2.reverse)) = false := by
  decide +kernel

theorem outer8_neg_alpha :
    fk8.outerN 8 8 rawGens8 words1_8 (decodeL W8.chars) outerRaw8.dropLast = false := by
  decide +kernel

end CertificateChecks.KernelHeis

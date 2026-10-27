module

public import Certificates.Kernel.TwoHS.E1
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS

theorem real_g2_0 : realK gamma2Word 1 gamma2Data 0 = true := by quickRfl
theorem real_g2_1 : realK gamma2Word 1 gamma2Data 1 = true := by quickRfl
theorem real_g2_2 : realK gamma2Word 1 gamma2Data 2 = true := by quickRfl

end CFSG.KD.TwoHS

end

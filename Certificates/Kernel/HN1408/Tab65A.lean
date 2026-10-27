module

public import Certificates.Kernel.HN1408.Tab65AChk
public import Certificates.Kernel.HN1408.M11Lem

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem tab65AOK_true : tab65AOK = true := by
  have eS := tabW_eq l65
  have eB := tabW_eq (wd := wordB) (by decide)
  have eR := tabW_eq l65R
  unfold tab65AOK
  rw [gensOK_true, wordOK_of l65, eB.1, eS.1, conjEqOK_of l65W eR.2 k65i eB.2 eS.2 k65c]
  rfl

end CFSG.KD.HN1408

end

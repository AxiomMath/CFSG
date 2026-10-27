module

public import Certificates.Kernel.SporSch.Co1.ElemDag
public meta import Certificates.Kernel.SporSch.Co1.GenDag
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_co1sortE CertificateChecks.KernelSporSch.Co1Elem.S CFSG.Sporadic.Co1Schreier.Native.elemDag
  CFSG.Sporadic.Co1Schreier.Data.elemIdx

namespace CertificateChecks.KernelSporSch.Co1Elem

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier.Native

theorem kE : eK AF S.MsP = true := by quickRfl
theorem sl0 : incSl AF S.MsP (81 * 0) 81 = true := by quickRfl
theorem sl1 : incSl AF S.MsP (81 * 1) 81 = true := by quickRfl
theorem sl2 : incSl AF S.MsP (81 * 2) 81 = true := by quickRfl
theorem sl3 : incSl AF S.MsP (81 * 3) 81 = true := by quickRfl
theorem sl4 : incSl AF S.MsP (81 * 4) 81 = true := by quickRfl
theorem sl5 : incSl AF S.MsP (81 * 5) 81 = true := by quickRfl
theorem sl6 : incSl AF S.MsP (81 * 6) 81 = true := by quickRfl
theorem sl7 : incSl AF S.MsP (81 * 7) 81 = true := by quickRfl
theorem sl8 : incSl AF S.MsP (81 * 8) 81 = true := by quickRfl

theorem slices : ∀ s < 9, incSl AF S.MsP (81 * s) 81 = true := by
  intro s hs
  rcases s with _ | _ | _ | _ | _ | _ | _ | _ | _ | s
  exacts [sl0, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, absurd hs (by omega)]

theorem e : eCheck = true := by
  have h : eCheck = eCheckP aRows := rfl
  rw [h, aRows_eq]
  exact eK_sound kE slices

end CertificateChecks.KernelSporSch.Co1Elem

end

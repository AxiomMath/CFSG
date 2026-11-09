module

public import Certificates.Kernel.ThDemp.Data
public import CFSG.Certificates.Kernel.ThDemp.Sound

set_option Elab.async false

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.Certificates.ThDemp

theorem res3_g0 : resChkR dempData 3 (dempData.frL 3 + 0) 1 = true := by
  decide +kernel

theorem res3_g1 : resChkR dempData 3 (dempData.frL 3 + 1) 1 = true := by
  decide +kernel

theorem res3_g2 : resChkR dempData 3 (dempData.frL 3 + 2) 1 = true := by
  decide +kernel

theorem res3_g3 : resChkR dempData 3 (dempData.frL 3 + 3) 1 = true := by
  decide +kernel

theorem res3_g4 : resChkR dempData 3 (dempData.frL 3 + 4) 1 = true := by
  decide +kernel

theorem res3_g5 : resChkR dempData 3 (dempData.frL 3 + 5) 1 = true := by
  decide +kernel

theorem res3_g6 : resChkR dempData 3 (dempData.frL 3 + 6) 1 = true := by
  decide +kernel

theorem res3_g7 : resChkR dempData 3 (dempData.frL 3 + 7) 1 = true := by
  decide +kernel

theorem res3_g8 : resChkR dempData 3 (dempData.frL 3 + 8) 1 = true := by
  decide +kernel

theorem res3_g9 : resChkR dempData 3 (dempData.frL 3 + 9) 1 = true := by
  decide +kernel

theorem res3_g10 : resChkR dempData 3 (dempData.frL 3 + 10) 1 = true := by
  decide +kernel

theorem res3_g11 : resChkR dempData 3 (dempData.frL 3 + 11) 1 = true := by
  decide +kernel

theorem res3_g12 : resChkR dempData 3 (dempData.frL 3 + 12) 1 = true := by
  decide +kernel

theorem res3_ok : resChk dempData 3 = true := by
  have hk : dempData.npr - dempData.frL 3 = 13 := by decide +kernel
  refine resChk_of_gens fun j hj => ?_
  rw [hk] at hj
  match j, hj with
  | 0, _ => exact res3_g0
  | 1, _ => exact res3_g1
  | 2, _ => exact res3_g2
  | 3, _ => exact res3_g3
  | 4, _ => exact res3_g4
  | 5, _ => exact res3_g5
  | 6, _ => exact res3_g6
  | 7, _ => exact res3_g7
  | 8, _ => exact res3_g8
  | 9, _ => exact res3_g9
  | 10, _ => exact res3_g10
  | 11, _ => exact res3_g11
  | 12, _ => exact res3_g12
  | _ + 13, h => omega

end CertificateChecks.KernelThDemp

end

module

public import Certificates.Kernel.ThDemp.Data
public import CFSG.Certificates.Kernel.ThDemp.Sound

set_option Elab.async false

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.Certificates.ThDemp

theorem res1_g0 : resChkR dempData 1 (dempData.frL 1 + 0) 1 = true := by
  decide +kernel

theorem res1_g1 : resChkR dempData 1 (dempData.frL 1 + 1) 1 = true := by
  decide +kernel

theorem res1_g2 : resChkR dempData 1 (dempData.frL 1 + 2) 1 = true := by
  decide +kernel

theorem res1_g3 : resChkR dempData 1 (dempData.frL 1 + 3) 1 = true := by
  decide +kernel

theorem res1_g4 : resChkR dempData 1 (dempData.frL 1 + 4) 1 = true := by
  decide +kernel

theorem res1_g5 : resChkR dempData 1 (dempData.frL 1 + 5) 1 = true := by
  decide +kernel

theorem res1_g6 : resChkR dempData 1 (dempData.frL 1 + 6) 1 = true := by
  decide +kernel

theorem res1_g7 : resChkR dempData 1 (dempData.frL 1 + 7) 1 = true := by
  decide +kernel

theorem res1_g8 : resChkR dempData 1 (dempData.frL 1 + 8) 1 = true := by
  decide +kernel

theorem res1_g9 : resChkR dempData 1 (dempData.frL 1 + 9) 1 = true := by
  decide +kernel

theorem res1_g10 : resChkR dempData 1 (dempData.frL 1 + 10) 1 = true := by
  decide +kernel

theorem res1_g11 : resChkR dempData 1 (dempData.frL 1 + 11) 1 = true := by
  decide +kernel

theorem res1_g12 : resChkR dempData 1 (dempData.frL 1 + 12) 1 = true := by
  decide +kernel

theorem res1_g13 : resChkR dempData 1 (dempData.frL 1 + 13) 1 = true := by
  decide +kernel

theorem res1_g14 : resChkR dempData 1 (dempData.frL 1 + 14) 1 = true := by
  decide +kernel

theorem res1_g15 : resChkR dempData 1 (dempData.frL 1 + 15) 1 = true := by
  decide +kernel

theorem res1_g16 : resChkR dempData 1 (dempData.frL 1 + 16) 1 = true := by
  decide +kernel

theorem res1_ok : resChk dempData 1 = true := by
  have hk : dempData.npr - dempData.frL 1 = 17 := by decide +kernel
  refine resChk_of_gens fun j hj => ?_
  rw [hk] at hj
  match j, hj with
  | 0, _ => exact res1_g0
  | 1, _ => exact res1_g1
  | 2, _ => exact res1_g2
  | 3, _ => exact res1_g3
  | 4, _ => exact res1_g4
  | 5, _ => exact res1_g5
  | 6, _ => exact res1_g6
  | 7, _ => exact res1_g7
  | 8, _ => exact res1_g8
  | 9, _ => exact res1_g9
  | 10, _ => exact res1_g10
  | 11, _ => exact res1_g11
  | 12, _ => exact res1_g12
  | 13, _ => exact res1_g13
  | 14, _ => exact res1_g14
  | 15, _ => exact res1_g15
  | 16, _ => exact res1_g16
  | _ + 17, h => omega

end CertificateChecks.KernelThDemp

end

module

public import Certificates.Kernel.ThDemp.Data
public import CFSG.Certificates.Kernel.ThDemp.Sound

set_option Elab.async false

public section

namespace CertificateChecks.KernelThDemp

open CFSG.KC.ThDemp CFSG.Certificates.ThDemp

theorem res2_g0 : resChkR dempData 2 (dempData.frL 2 + 0) 1 = true := by
  decide +kernel

theorem res2_g1 : resChkR dempData 2 (dempData.frL 2 + 1) 1 = true := by
  decide +kernel

theorem res2_g2 : resChkR dempData 2 (dempData.frL 2 + 2) 1 = true := by
  decide +kernel

theorem res2_g3 : resChkR dempData 2 (dempData.frL 2 + 3) 1 = true := by
  decide +kernel

theorem res2_g4 : resChkR dempData 2 (dempData.frL 2 + 4) 1 = true := by
  decide +kernel

theorem res2_g5 : resChkR dempData 2 (dempData.frL 2 + 5) 1 = true := by
  decide +kernel

theorem res2_g6 : resChkR dempData 2 (dempData.frL 2 + 6) 1 = true := by
  decide +kernel

theorem res2_g7 : resChkR dempData 2 (dempData.frL 2 + 7) 1 = true := by
  decide +kernel

theorem res2_g8 : resChkR dempData 2 (dempData.frL 2 + 8) 1 = true := by
  decide +kernel

theorem res2_g9 : resChkR dempData 2 (dempData.frL 2 + 9) 1 = true := by
  decide +kernel

theorem res2_g10 : resChkR dempData 2 (dempData.frL 2 + 10) 1 = true := by
  decide +kernel

theorem res2_g11 : resChkR dempData 2 (dempData.frL 2 + 11) 1 = true := by
  decide +kernel

theorem res2_g12 : resChkR dempData 2 (dempData.frL 2 + 12) 1 = true := by
  decide +kernel

theorem res2_g13 : resChkR dempData 2 (dempData.frL 2 + 13) 1 = true := by
  decide +kernel

theorem res2_g14 : resChkR dempData 2 (dempData.frL 2 + 14) 1 = true := by
  decide +kernel

theorem res2_ok : resChk dempData 2 = true := by
  have hk : dempData.npr - dempData.frL 2 = 15 := by decide +kernel
  refine resChk_of_gens fun j hj => ?_
  rw [hk] at hj
  match j, hj with
  | 0, _ => exact res2_g0
  | 1, _ => exact res2_g1
  | 2, _ => exact res2_g2
  | 3, _ => exact res2_g3
  | 4, _ => exact res2_g4
  | 5, _ => exact res2_g5
  | 6, _ => exact res2_g6
  | 7, _ => exact res2_g7
  | 8, _ => exact res2_g8
  | 9, _ => exact res2_g9
  | 10, _ => exact res2_g10
  | 11, _ => exact res2_g11
  | 12, _ => exact res2_g12
  | 13, _ => exact res2_g13
  | 14, _ => exact res2_g14
  | _ + 15, h => omega

end CertificateChecks.KernelThDemp

end

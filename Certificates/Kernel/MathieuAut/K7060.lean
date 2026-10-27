module

public import Certificates.Data.Kernel.MathieuAut.ColsK
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CertificateChecks.KernelMathieuAut

open CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu CFSG.Monster.Code CFSG.Decide

theorem k7060_mem22 : ((cent22H ++ cent22S).all fun a =>
    a.size == 24 && inAutK a && (a[0]! == 0 && a[1]! == 1)) = true := by
  decide +kernel

theorem k7060_fix0_22 : (cent22H.all fun a => actM (cols10 a.toList) 48 == 48) = true := by
  decide +kernel

theorem k7060_fix22 :
    fixAll (cent22H.map fun a => cols10 a.toList) 1024 (· == ·) (fun m => m == 0 || m == 48) =
      true := by
  decide +kernel

theorem k7060_span22 : spanAll 1024 (cent22S.map fun a => actM (cols10 a.toList) 48) = true := by
  decide +kernel

theorem k7060_o2Masks22 : bitsetNodup o2Masks22 = true := by
  decide +kernel

theorem k7060_swap01 : ∃ i < 12, syndM (permM swap01Arr (Bmask i)) ≠ 0 := by
  decide +kernel

theorem k7060_mem11 : ((cent11H ++ cent11S).all fun a =>
    a.size == 24 && inAutK a && a[0]! == 0) = true := by
  decide +kernel

theorem k7060_fix0_11 : (cent11H.all fun a => actM (cols11 a.toList) 95 == 95) = true := by
  decide +kernel

theorem k7060_fix11 :
    fixAll (cent11H.map fun a => cols11 a.toList) 2048 (· == ·) (fun m => m == 0 || m == 95) =
      true := by
  decide +kernel

theorem k7060_span11 : spanAll 2048 (cent11S.map fun a => actM (cols11 a.toList) 95) = true := by
  decide +kernel

theorem k7060_o2Masks24 : bitsetNodup o2Masks24 = true := by
  decide +kernel

end CertificateChecks.KernelMathieuAut

end

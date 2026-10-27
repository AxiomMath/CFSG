module

public import Certificates.Data.Kernel.MathieuAut.ColsK
public import CFSG.Quasithin.Background.HMathieuCodeCentInputs

public section

namespace CertificateChecks.KernelMathieuAut

open CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu

theorem k7061_memC11 : ((centC11H ++ centC11S).all fun a =>
    a.size == 24 && inAutK a && a[0]! == 0) = true := by
  decide +kernel

theorem k7061_fix0C11 :
    (centC11H.all fun a => actM (colsC11 a.toList) 1299 == 1299) = true := by
  decide +kernel

theorem k7061_fixC11 :
    fixAll (centC11H.map fun a => colsC11 a.toList) 2048 (· == ·)
      (fun m => m == 0 || m == 1299) = true := by
  decide +kernel

theorem k7061_spanC11 :
    spanAll 2048 (centC11S.map fun a => actM (colsC11 a.toList) 1299) = true := by
  decide +kernel

theorem k7061_memC10 : ((centC10H ++ centC10S).all fun a =>
    a.size == 24 && inAutK a && (a[0]! == 0 && a[1]! == 1)) = true := by
  decide +kernel

theorem k7061_fix0C10 : (centC10H.all fun a => actM (colsC10 a.toList) 608 == 608) = true := by
  decide +kernel

theorem k7061_fixC10 :
    fixAll (centC10H.map fun a => colsC10 a.toList) 1024 (· == ·)
      (fun m => m == 0 || m == 608) = true := by
  decide +kernel

theorem k7061_spanC10 :
    spanAll 1024 (centC10S.map fun a => actM (colsC10 a.toList) 608) = true := by
  decide +kernel

theorem k7061_syndCols : syndCols.length = 24 ∧ transOK syndCols = true := by
  decide +kernel

theorem k7061_cc10Cols : cc10Cols.length = 24 ∧ transOK cc10Cols = true := by
  decide +kernel

end CertificateChecks.KernelMathieuAut

end

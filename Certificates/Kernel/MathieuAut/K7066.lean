module

public import Certificates.Data.Kernel.MathieuAut.ColsK
public import CFSG.Quasithin.Background.HMathieuO2CertInputs

public section

namespace CertificateChecks.KernelMathieuAut

open CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu

theorem k7066_mem10 : ((o2H0_10 ++ o2H1_10 ++ o2S_10 ++ o2C_10.map Prod.fst).all fun a =>
    a.size == 24 && inAutK a && (a[0]! == 0 && a[1]! == 1 && a[2]! == 2)) = true := by
  decide +kernel

theorem k7066_fix0_10 :
    fixAll (o2H0_10.map fun a => cols10 a.toList) (2 ^ 10) (· == ·)
      (fun m => m == 0 || m == 48) = true := by
  decide +kernel

theorem k7066_h1_10 : (o2H1_10.all fun a =>
    actM (cols10 a.toList) 16 == 16 || actM (cols10 a.toList) 16 == 16 ^^^ 48) = true := by
  decide +kernel

theorem k7066_fix1_10 :
    fixAll (o2H1_10.map fun a => cols10 a.toList) (2 ^ 10) (fun x m => x == m || x == m ^^^ 48)
      (fun m => m == 0 || m == 48 || m == 16 || m == 16 ^^^ 48) = true := by
  decide +kernel

theorem k7066_span10 :
    spanAll (2 ^ 10) (48 :: o2S_10.map fun a => actM (cols10 a.toList) 16) = true := by
  decide +kernel

theorem k7066_comm10 :
    spanAll (2 ^ 10) (o2C_10.map fun p => actM (cols10 p.1.toList) p.2 ^^^ p.2) = true := by
  decide +kernel

theorem k7066_pair10 : actM cc10Cols (pairMask 0 ((2 : Fin 24) : ℕ)) = 48 := by
  decide +kernel

theorem k7066_mem11 : ((o2H0_11 ++ o2H1_11 ++ o2S_11 ++ o2C_11.map Prod.fst).all fun a =>
    a.size == 24 && inAutK a && (a[0]! == 0 && a[1]! == 1)) = true := by
  decide +kernel

theorem k7066_fix0_11 :
    fixAll (o2H0_11.map fun a => cols11 a.toList) (2 ^ 11) (· == ·)
      (fun m => m == 0 || m == 95) = true := by
  decide +kernel

theorem k7066_h1_11 : (o2H1_11.all fun a =>
    actM (cols11 a.toList) 63 == 63 || actM (cols11 a.toList) 63 == 63 ^^^ 95) = true := by
  decide +kernel

theorem k7066_fix1_11 :
    fixAll (o2H1_11.map fun a => cols11 a.toList) (2 ^ 11) (fun x m => x == m || x == m ^^^ 95)
      (fun m => m == 0 || m == 95 || m == 63 || m == 63 ^^^ 95) = true := by
  decide +kernel

theorem k7066_span11 :
    spanAll (2 ^ 11) (95 :: o2S_11.map fun a => actM (cols11 a.toList) 63) = true := by
  decide +kernel

theorem k7066_comm11 :
    spanAll (2 ^ 11) (o2C_11.map fun p => actM (cols11 p.1.toList) p.2 ^^^ p.2) = true := by
  decide +kernel

theorem k7066_pair11 : pairImg11 ((0 : Fin 24) : ℕ) ((1 : Fin 24) : ℕ) = 95 := by
  decide +kernel

end CertificateChecks.KernelMathieuAut

end

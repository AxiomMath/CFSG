module

public import Certificates.Kernel.ONCover.Dce.FoldQ0
public import Certificates.Kernel.ONCover.Dce.FoldQ1
public import Certificates.Kernel.ONCover.Dce.FoldQ2
public import Certificates.Kernel.ONCover.Dce.FoldQ3
public import Certificates.Kernel.ONCover.Dce.FoldQ4
public import Certificates.Kernel.ONCover.Dce.FoldQ5
public import Certificates.Kernel.ONCover.Dce.FoldQ6
public import Certificates.Kernel.ONCover.Dce.FoldQ7
public import Certificates.Kernel.ONCover.Dce.FoldQ8
public import Certificates.Kernel.ONCover.Dce.FoldQ9
public import Certificates.Kernel.ONCover.Dce.FoldQ10
public import Certificates.Kernel.ONCover.Dce.FoldQ11
public import Certificates.Kernel.ONCover.Dce.FoldQ12
public import Certificates.Kernel.ONCover.Dce.FoldQ13
public import Certificates.Kernel.ONCover.Dce.FoldQ14
public import Certificates.Kernel.ONCover.Dce.FoldQ15
public import Certificates.Kernel.ONCover.Dce.FoldQ16
public import Certificates.Kernel.ONCover.Dce.FoldQ17
public import Certificates.Kernel.ONCover.Dce.FoldQ18
public import Certificates.Kernel.ONCover.Dce.FoldQ19
public import CFSG.Certificates.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.ONCoverDce3

open CFSG.KC.TwDce3

theorem nb_eq : NB = 4 := by decide +kernel

theorem fq (a n S S' : ℕ) (h : CFSG.KC.TwDce3Q.foldIs (CFSG.KC.TwDce3Q.isOneQ4 PB F BS)
    INVM NT PSF PSB RD RW RA WD RJ a n S S' = true) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S = S' :=
  CFSG.Certificates.TwDce3.FoldQ.fold_of4 PB F INVM BS NB NT PSF PSB RD RW RA WD RJ nb_eq h

theorem fold0 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 1809 1 = 164 :=
  fq 0 1809 1 164 foldq0
theorem fold1 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 1809 1459 164 = 279 :=
  fq 1809 1459 164 279 foldq1
theorem fold2 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 3268 1297 279 = 560 :=
  fq 3268 1297 279 560 foldq2
theorem fold3 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 4565 1887 560 = 775 :=
  fq 4565 1887 560 775 foldq3
theorem fold4 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 6452 2879 775 = 775 :=
  fq 6452 2879 775 775 foldq4
theorem fold5 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 9331 1154 775 = 775 :=
  fq 9331 1154 775 775 foldq5
theorem fold6 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 10485 1084 775 = 775 :=
  fq 10485 1084 775 775 foldq6
theorem fold7 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 11569 1234 775 = 775 :=
  fq 11569 1234 775 775 foldq7
theorem fold8 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 12803 907 775 = 775 :=
  fq 12803 907 775 775 foldq8
theorem fold9 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 13710 578 775 = 775 :=
  fq 13710 578 775 775 foldq9
theorem fold10 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 14288 948 775 = 775 :=
  fq 14288 948 775 775 foldq10
theorem fold11 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 15236 838 775 = 775 :=
  fq 15236 838 775 775 foldq11
theorem fold12 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 16074 728 775 = 775 :=
  fq 16074 728 775 775 foldq12
theorem fold13 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 16802 378 775 = 775 :=
  fq 16802 378 775 775 foldq13
theorem fold14 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 17180 387 775 = 775 :=
  fq 17180 387 775 775 foldq14
theorem fold15 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 17567 324 775 = 775 :=
  fq 17567 324 775 775 foldq15
theorem fold16 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 17891 284 775 = 775 :=
  fq 17891 284 775 775 foldq16
theorem fold17 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 18175 262 775 = 775 :=
  fq 18175 262 775 775 foldq17
theorem fold18 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 18437 254 775 = 775 :=
  fq 18437 254 775 775 foldq18
theorem fold19 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 18691 243 775 = 775 :=
  fq 18691 243 775 775 foldq19

end CFSG.KD.ONCoverDce3

end

module

public import Certificates.Kernel.Fi23U3.Dce.FoldQ0
public import Certificates.Kernel.Fi23U3.Dce.FoldQ1
public import Certificates.Kernel.Fi23U3.Dce.FoldQ2
public import Certificates.Kernel.Fi23U3.Dce.FoldQ3
public import Certificates.Kernel.Fi23U3.Dce.FoldQ4
public import Certificates.Kernel.Fi23U3.Dce.FoldQ5
public import Certificates.Kernel.Fi23U3.Dce.FoldQ6
public import Certificates.Kernel.Fi23U3.Dce.FoldQ7
public import Certificates.Kernel.Fi23U3.Dce.FoldQ8
public import Certificates.Kernel.Fi23U3.Dce.FoldQ9
public import CFSG.Certificates.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce3

theorem nb_eq : NB = 4 := by decide +kernel

theorem fq (a n S S' : ℕ) (h : CFSG.KC.TwDce3Q.foldIs (CFSG.KC.TwDce3Q.isOneQ4 PB F BS)
    INVM NT PSF PSB RD RW RA WD RJ a n S S' = true) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S = S' :=
  CFSG.Certificates.TwDce3.FoldQ.fold_of4 PB F INVM BS NB NT PSF PSB RD RW RA WD RJ nb_eq h

theorem fold0 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 5307 1 = 725 :=
  fq 0 5307 1 725 foldq0
theorem fold1 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 5307 5343 725 = 1849 :=
  fq 5307 5343 725 1849 foldq1
theorem fold2 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 10650 5057 1849 = 2730 :=
  fq 10650 5057 1849 2730 foldq2
theorem fold3 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 15707 3238 2730 = 2730 :=
  fq 15707 3238 2730 2730 foldq3
theorem fold4 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 18945 5538 2730 = 2735 :=
  fq 18945 5538 2730 2735 foldq4
theorem fold5 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 24483 6075 2735 = 2735 :=
  fq 24483 6075 2735 2735 foldq5
theorem fold6 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 30558 5081 2735 = 2735 :=
  fq 30558 5081 2735 2735 foldq6
theorem fold7 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 35639 4794 2735 = 2735 :=
  fq 35639 4794 2735 2735 foldq7
theorem fold8 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 40433 2474 2735 = 2735 :=
  fq 40433 2474 2735 2735 foldq8
theorem fold9 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 42907 1103 2735 = 2735 :=
  fq 42907 1103 2735 2735 foldq9

end CFSG.KD.Fi23Dce3

end

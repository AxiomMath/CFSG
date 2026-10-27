module

public import Certificates.Kernel.TwistDce3.ON.FoldQ0
public import Certificates.Kernel.TwistDce3.ON.FoldQ1
public import Certificates.Kernel.TwistDce3.ON.FoldQ2
public import Certificates.Kernel.TwistDce3.ON.FoldQ3
public import Certificates.Kernel.TwistDce3.ON.FoldQ4
public import Certificates.Kernel.TwistDce3.ON.FoldQ5
public import CFSG.Certificates.Kernel.TwistDce3.FoldQ4

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce3

theorem nb_eq : NB = 4 := by decide +kernel

theorem fq (a n S S' : ℕ) (h : CFSG.KC.TwDce3Q.foldIs (CFSG.KC.TwDce3Q.isOneQ4 PB F BS)
    INVM NT PSF PSB RD RW RA WD RJ a n S S' = true) :
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S = S' :=
  CFSG.Certificates.TwDce3.FoldQ.fold_of4 PB F INVM BS NB NT PSF PSB RD RW RA WD RJ nb_eq h

theorem fold0 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 1670 1 = 131 :=
  fq 0 1670 1 131 foldq0
theorem fold1 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 1670 1307 131 = 152 :=
  fq 1670 1307 131 152 foldq1
theorem fold2 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 2977 617 152 = 152 :=
  fq 2977 617 152 152 foldq2
theorem fold3 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 3594 421 152 = 152 :=
  fq 3594 421 152 152 foldq3
theorem fold4 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 4015 352 152 = 152 :=
  fq 4015 352 152 152 foldq4
theorem fold5 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 4367 258 152 = 152 :=
  fq 4367 258 152 152 foldq5

end CFSG.KD.ONDce3

end

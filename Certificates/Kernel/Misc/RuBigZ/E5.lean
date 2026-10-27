module

public import Certificates.Data.Kernel.Misc.RuBigZE
public import Certificates.Kernel.Misc.RuBigZ.Data
public import Certificates.Kernel.Misc.RuBigZ.DataE
public import Certificates.Kernel.SporSch.Ru.CData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Enum CFSG.KC.Misc.RuBigZ CertificateChecks.KernelSporSch

@[expose] noncomputable def ch7233e5_ (q : Nat) : Bool :=
  elChk RuCS.LR RuCS.TR R Q AL5 EL5 5 (Nat.mul 32 q) 32

@[expose] noncomputable def alOf (X a : Nat) : Nat :=
  nIf(Nat.beq X 0, AL0 a, nIf(Nat.beq X 1, AL1 a, nIf(Nat.beq X 2, AL2 a,
    nIf(Nat.beq X 3, AL3 a, nIf(Nat.beq X 4, AL4 a, AL5 a)))))

@[expose] noncomputable def alN (X : Nat) : Nat :=
  nIf(Nat.beq X 0, 512, nIf(Nat.beq X 1, 64, nIf(Nat.beq X 2, 128,
    nIf(Nat.beq X 3, 128, nIf(Nat.beq X 4, 64, 256)))))

@[expose] noncomputable def ch7233al_ (X : Nat) : Bool :=
  alChk RuCS.LR L (alOf X) X (alN X)

end CertificateChecks.KernelMisc.RuBigZ

#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233e5_ 0 8
#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233al_ 0 6

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233lk :
    CFSG.KC.Misc.RuBigZ.l0kChk CertificateChecks.KernelMisc.RuBigZ.L 1920 = true := by quickRfl

end

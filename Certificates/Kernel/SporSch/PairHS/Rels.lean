module

public import Certificates.Kernel.SporSch.PairHS.RelsData
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.SporSch.RuPres
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PHSCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def G (i : Nat) : Nat := nIf(Nat.beq i 0, PHSC.S 0, PHSC.S 1)

@[expose] noncomputable def GI (i : Nat) : Nat := nIf(Nat.beq i 0, PHSC.SI 0, PHSC.SI 1)

@[expose] noncomputable def KK (r : Nat) : Nat :=
  Nat.div (Nat.add (lenL (wAt CFSG.KC.HSK.relsLit r)) 3) 4

@[expose] noncomputable def jobF (j : Nat) : Bool :=
  strictB (Nat.div j 10) (fun r => strictB (Nat.mod j 10) (fun q =>
    bIf(Nat.blt q (KK r),
      Nat.beq (wordPKFrom 3850 12 G GI (takeL 4 (dropL (Nat.mul 4 q) (wAt CFSG.KC.HSK.relsLit r)))
        (PHSR.TT (Nat.add (Nat.mul 10 r) (Nat.succ q)))) (PHSR.TT (Nat.add (Nat.mul 10 r) q)), true)))

@[expose] noncomputable def endOK (r : Nat) : Bool :=
  bAnd(Nat.ble (KK r) 10, Nat.beq (PHSR.TT (Nat.add (Nat.mul 10 r) (KK r))) (pidn 3850 12))

end CertificateChecks.KernelSporSch.PHSCheck

#kss_each CertificateChecks.KernelSporSch.PHSCheck.JC CertificateChecks.KernelSporSch.PHSCheck.jobF 130
#kss_each CertificateChecks.KernelSporSch.PHSCheck.EC CertificateChecks.KernelSporSch.PHSCheck.endOK 13

namespace CertificateChecks.KernelSporSch.PHSCheck

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem tgtRel : allN 13 (fun r => Nat.beq (PHSR.TT (Nat.mul 10 r)) (pidn 3850 12)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.PHSCheck

end

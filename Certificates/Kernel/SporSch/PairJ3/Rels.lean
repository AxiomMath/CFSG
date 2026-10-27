module

public import Certificates.Kernel.SporSch.PairJ3.RelsData
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.SporSch.RuPres
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.PJ3Check

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def G (i : Nat) : Nat := nIf(Nat.beq i 0, PJ3.S 0, PJ3.S 1)

@[expose] noncomputable def GI (i : Nat) : Nat := nIf(Nat.beq i 0, PJ3.SI 0, PJ3.SI 1)

@[expose] noncomputable def KK (r : Nat) : Nat := Nat.div (Nat.add (lenL (wAt CFSG.KC.J3A.rels r)) 3) 4

@[expose] noncomputable def jobF (j : Nat) : Bool :=
  strictB (Nat.div j 16) (fun r => strictB (Nat.mod j 16) (fun q =>
    bIf(Nat.blt q (KK r),
      Nat.beq (wordPKFrom 6156 13 G GI (takeL 4 (dropL (Nat.mul 4 q) (wAt CFSG.KC.J3A.rels r)))
        (PJ3R.TT (Nat.add (Nat.mul 16 r) (Nat.succ q)))) (PJ3R.TT (Nat.add (Nat.mul 16 r) q)), true)))

@[expose] noncomputable def endOK (r : Nat) : Bool :=
  bAnd(Nat.ble (KK r) 16, Nat.beq (PJ3R.TT (Nat.add (Nat.mul 16 r) (KK r))) (pidn 6156 13))

end CertificateChecks.KernelSporSch.PJ3Check

#kss_each CertificateChecks.KernelSporSch.PJ3Check.JC CertificateChecks.KernelSporSch.PJ3Check.jobF 128
#kss_each CertificateChecks.KernelSporSch.PJ3Check.EC CertificateChecks.KernelSporSch.PJ3Check.endOK 8

namespace CertificateChecks.KernelSporSch.PJ3Check

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CertificateChecks.KernelSporSch

theorem tgtRel : allN 8 (fun r => Nat.beq (PJ3R.TT (Nat.mul 16 r)) (pidn 6156 13)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.PJ3Check

end

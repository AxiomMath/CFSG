module

public import Certificates.Kernel.SporSch.Ru.PresData
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.RowsGen
public import Certificates.Data.Kernel.SporSch.RuPres
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuPres

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuPD

@[expose] noncomputable def Ug (i : Nat) : Nat := nIf(Nat.blt i 3, U i, pidn 4060 12)

@[expose] noncomputable def UIg (i : Nat) : Nat := nIf(Nat.blt i 3, UI i, pidn 4060 12)

@[expose] noncomputable def KK (r : Nat) : Nat := Nat.div (Nat.add (lenL (wAt WS r)) 19) 20

@[expose] noncomputable def jobF (j : Nat) : Bool :=
  strictB (Nat.div j 10) (fun r => strictB (Nat.mod j 10) (fun q =>
    bIf(Nat.blt q (KK r),
      Nat.beq (wordPKFrom 4060 12 Ug UIg (takeL 20 (dropL (Nat.mul 20 q) (wAt WS r)))
        (TT (Nat.add (Nat.mul 16 r) (Nat.succ q)))) (TT (Nat.add (Nat.mul 16 r) q)), true)))

@[expose] noncomputable def endOK (r : Nat) : Bool :=
  bAnd(Nat.ble (KK r) 10, Nat.beq (TT (Nat.add (Nat.mul 16 r) (KK r))) (pidn 4060 12))

end CertificateChecks.KernelSporSch.RuPres

#kss_each CertificateChecks.KernelSporSch.RuPres.JC CertificateChecks.KernelSporSch.RuPres.jobF 140
#kss_each CertificateChecks.KernelSporSch.RuPres.EC CertificateChecks.KernelSporSch.RuPres.endOK 14

namespace CertificateChecks.KernelSporSch.RuPres

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuPD

theorem gensOK : allN 3 (fun i => bAnd(permOK 4060 12 (mask 12) (4060 * 12) (U i) (UI i),
    bAnd(canonK 4060 12 (mask 12) (4060 * 12) (U i), canonK 4060 12 (mask 12) (4060 * 12) (UI i))))
    = true := by quickRfl

theorem idCanon : canonK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) = true := by quickRfl

theorem tgtRel : allN 12 (fun r => Nat.beq (TT (Nat.mul 16 r)) (pidn 4060 12)) = true := by
  quickRfl

theorem tgtA0 : Nat.beq (TT 192) A0 = true := by quickRfl

theorem tgtA1 : Nat.beq (TT 208) A1 = true := by quickRfl

end CertificateChecks.KernelSporSch.RuPres

end

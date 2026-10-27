module

public import Certificates.Data.Kernel.J4Loc.Trio
public import Certificates.Kernel.J4Loc.TrioData
public import Certificates.Kernel.J4Q.LocData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.MatData
public import CFSG.Sporadic.J4.QTData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KD.J4Loc CFSG.KD.J4Q

@[expose] noncomputable def us4177 : List Nat := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

theorem ch4177_mat : allR 3 (fun k => Nat.beq
    (mulJ c rm (mulJ c rm ML_4 (etaK c rm one us4177 (getN 0 [965, 1979, 165] k))) MLI_4)
    (etaK c rm one us4177 (getN 0 [1243, 1979, 165] k))) = true := by
  quickRfl

theorem ch4177_oct : andB (Nat.beq (keyK (spanK [965, 1979, 165]))
      (keyK [0, 965, 1979, 1243, 165, 864, 1822, 1150]))
    (andB (Nat.beq (keyK (wordImg CFSG.Sporadic.J4.QT.letterRows I5W
        [0, 422, 553, 911, 1131, 1485, 1602, 2020])) (keyK [0, 965, 1979, 1243, 165, 864, 1822, 1150]))
      (andB (Nat.blt I5I 3795)
        (Nat.beq (keyK (octL (fld 80 TRK I5I))) (keyK [0, 965, 1979, 1243, 165, 864, 1822, 1150])))) =
    true := by
  quickRfl

end CertificateChecks.KernelJ4Loc

end

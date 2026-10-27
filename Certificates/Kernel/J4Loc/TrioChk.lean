module

public import Certificates.Data.Kernel.J4Loc.Trio
public import Certificates.Kernel.J4Loc.TrioData
public import CFSG.Sporadic.J4.QTData
public import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KD.J4Loc

@[expose] noncomputable def ch4174T (k : Nat) : Bool :=
  octBlk CFSG.Sporadic.J4.QT.letterRows TRK TRR (nat_lit 3795) TRI0 k

#j4q_all CFSG.KD.J4Loc.TRC CertificateChecks.KernelJ4Loc.ch4174T 119

theorem ch4174_v0 : andB (Nat.blt TRI0 3795)
    (eqLK (octL (fld 80 TRK TRI0)) [0, 422, 553, 911, 1131, 1485, 1602, 2020]) = true := by
  quickRfl

end CertificateChecks.KernelJ4Loc

end

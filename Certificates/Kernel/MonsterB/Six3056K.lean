
module

public import CFSG.Certificates.Kernel.SortTreeSlice
public import Certificates.Kernel.MonsterB.Six3056Data
public import CFSG.Monster.B.TwoA.Co2Inv.SixCertInputs
public import Certificates.Data.Kernel.MonsterB.QForm
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

public section

namespace CertificateChecks.Six3056

open CFSG.KC.SortTree CFSG.KLie.CT CFSG.KC.QForm CFSG.Monster.B.TwoA.Co2Inv

set_option maxRecDepth 100000

@[expose] noncomputable def act6R (k n : Nat) : Nat :=
  orN 6 fun t => Nat.shiftLeft (actB TT k (fget n t 22)) (Nat.mul 22 t)

@[expose] noncomputable def recS : Nat → Nat := recT S 6 156

@[expose] noncomputable def edgeS (i k : Nat) : Nat := fget (recT SE 6 300 i) k 15

@[expose] noncomputable def mat (k : Nat) : Nat := fget MM k 484

theorem kTab : tabOK TT mat 20 = true := by quickRfl

@[expose] noncomputable def tF (s : Nat) : Bool :=
  treeSl act6R 20 valid6 root6 recS 23040 132 4 15 64 (60 * s) 60

@[expose] noncomputable def cF (s : Nat) : Bool := closeSl act6R 20 recS edgeS 23040 132 64 (15 * s) 15

#kc_each_unfold tF 0 6 as CertificateChecks.Six3056.t
#kc_each_unfold cF 0 24 as CertificateChecks.Six3056.c

end CertificateChecks.Six3056

end

module

public import Certificates.Kernel.L52Insp443.MChk
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def recUnits (L : List Rec) : Bool :=
  allK (fun r => andB (unitM r.2.1) (unitM r.2.2.1)) L

@[expose] noncomputable def ch725109e (z : Nat) : Bool := recUnits (D.oZ.getD z [])

@[expose] noncomputable def ch725109f (w : Nat) : Bool := recUnits (D.oW.getD w [])

@[expose] noncomputable def ch725109g (_ : Nat) : Bool :=
  andB (Nat.beq (List.length D.gs) (nat_lit 2)) (andB (Nat.beq (List.length D.gis) (nat_lit 2))
    (andB (allK unitM D.gs) (allK unitM D.gis)))

#kc_each ch725109e 0 7
#kc_each ch725109f 0 2
#kc_each ch725109g 0 1

theorem ch725109n_rec : notB (recUnits ((0, 0, idK, 0, 0) :: D.oZ.getD 0 [])) = true := by
  quickRfl

end CertificateChecks.KernelL52I

end

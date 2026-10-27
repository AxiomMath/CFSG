module

public import Certificates.Kernel.MonsterB.Orb3132Rec
public import Certificates.Kernel.MonsterB.Co2Vecs
public import CFSG.Monster.B.TwoA.Unitary.NData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Orb3132

open CFSG.KLie.CT CFSG.KC.QForm CFSG.KC.U6Orb CFSG.KC.SortTree CertificateChecks.KernelMonB
  CFSG.Monster.B.TwoA.Unitary

set_option maxRecDepth 100000

@[expose] noncomputable def om (j : Nat) : Nat := fget (Co2V.F 0) j (nat_lit 24)

@[expose] noncomputable def pi (k j : Nat) : Nat := fget (PP (Nat.mul (nat_lit 2) k)) j (nat_lit 12)

@[expose] noncomputable def rho (k j : Nat) : Nat :=
  fget (PP (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1))) j (nat_lit 12)

@[expose] noncomputable def fP (v j : Nat) : Bool :=
  andB (Nat.beq (bK U v (om j)) (nat_lit 0)) (Nat.beq (bK U (nat_lit 6144) (om j)) (nat_lit 0))

@[expose] noncomputable def fK (v : Nat) : Nat :=
  sumN (nat_lit 2300) fun j => nIf(fP v j, nat_lit 1, nat_lit 0)

theorem kMat :
    Nat.beq MM (packL 484 (mapL (fun a => packL 22 a.toList) n6RowArr.toList)) = true := by
  quickRfl

theorem kRow : shapeL 22 (pw2 22) n6RowArr.toList = true := by quickRfl

theorem kSize : Nat.beq n6RowArr.size 17 = true := by quickRfl

theorem kTab : tabOK TT mat 17 = true := by quickRfl

theorem kInv : allN 17 (fun k => invK U (mat k)) = true := by quickRfl

theorem kSig : allN 17 (fun k => Nat.beq (actK (mat k) 6144) 6144) = true := by quickRfl

@[expose] noncomputable def repOK (r : Nat) : Bool :=
  andB (Nat.beq (bK U (nat_lit 6144) r) (nat_lit 1)) (Nat.beq (qK U r) (nat_lit 0))

theorem kForm : andB (Nat.beq (qK U 6144) 0) (andB (Nat.beq (bK U 6144 32) 1)
    (andB (repOK 60) (andB (repOK 39) (andB (repOK 35) (repOK 32))))) = true := by
  quickRfl

theorem kOm : andB (allN 2300 fun j => Nat.blt (om j) (pw2 22))
    (allN 17 fun k => allN 2300 fun j => andB (Nat.blt (pi k j) 2300)
      (andB (Nat.beq (rho k (pi k j)) j) (Nat.beq (act k (om j)) (om (pi k j))))) = true := by
  quickRfl

theorem kF : andB (Nat.beq (fK 60) 324) (andB (Nat.beq (fK 39) 420)
    (andB (Nat.beq (fK 35) 452) (Nat.beq (fK 32) 484))) = true := by quickRfl

theorem kRoots : andB (Nat.beq (valF 22 (rec60 0)) 60) (andB (Nat.beq (valF 22 (rec39 0)) 39)
    (andB (Nat.beq (valF 22 (rec35 0)) 35) (Nat.beq (valF 22 (rec32 0)) 32))) = true := by
  quickRfl

end CertificateChecks.Orb3132

end

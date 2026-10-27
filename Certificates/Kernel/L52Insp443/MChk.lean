module

public import Certificates.Kernel.L52Insp443.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I

@[expose] noncomputable def unitM (c : Nat) : Bool :=
  andB (Nat.blt c (nat_lit 33554432)) (Nat.beq (rankK c) (nat_lit 5))

@[expose] noncomputable def mChk (L wS a0 a1 : List Nat) (τ : Nat) : Bool :=
  andB (unitM τ) (andB (nodupK L) (andB (Nat.beq (List.length L) (nat_lit 128))
    (andB (allK (fun c => andB (unitM c) (allK (commK c) a0)) L)
      (allK (fun s => allK (commK s) a1) wS))))

@[expose] noncomputable def ch725109m (w : Nat) : Bool :=
  mChk (List.append (D.wS.getD w []) (mapMulK (D.tau.getD w 0) (D.wS.getD w [])))
    (D.wS.getD w []) (D.a0B.getD w []) (D.a1B.getD w []) (D.tau.getD w 0)

#kc_each ch725109m 0 2

theorem ch725109n_m : notB (mChk (List.append (D.wS.getD 0 []) (mapMulK idK (D.wS.getD 0 [])))
    (D.wS.getD 0 []) (D.a0B.getD 0 []) (D.a1B.getD 0 []) idK) = true := by
  quickRfl

end CertificateChecks.KernelL52I

end

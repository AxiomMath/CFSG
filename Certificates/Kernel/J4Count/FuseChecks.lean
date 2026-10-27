module

public import Certificates.Data.Kernel.SporSch.J4SPairK
public import Certificates.Data.Kernel.SporSch.J4SRun
public import Certificates.Kernel.J4Q.MatData
public import CFSG.Sporadic.Schreier.J4SData
public import Certificates.Data.CFSGNative.H13.J4Elems
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count.Fuse

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B

@[expose] noncomputable def pm (P Q : Nat × Nat) : Nat × Nat := (mulJ c rm P.1 Q.1, mulJ c rm Q.2 P.2)

@[expose] noncomputable def pinv (P : Nat × Nat) : Nat × Nat := (P.2, P.1)

@[expose] noncomputable def ppow (P : Nat × Nat) (e : Nat) : Nat × Nat :=
  (powJ c rm one P.1 e, powJ c rm one P.2 e)

@[expose] noncomputable def INIT : List Nat :=
  [one, A, B, one, one, one, one, one, one, one, A, Bi, one, one, one, one, one, one]

@[expose] noncomputable def RG : List Nat := runPK c rm one INIT CFSG.Sporadic.J4Schreier.typeIIProg

@[expose] noncomputable def reg (r : Nat) : Nat × Nat := (getN one RG r, getN one RG (Nat.add 9 r))

@[expose] noncomputable def DK : Nat × Nat := pm (pm (ppow (pm (reg 2) (reg 1)) 4) (pinv (reg 2))) (reg 1)

@[expose] noncomputable def ZK : Nat × Nat := ppow (pm (pm (pm (reg 2) (pinv DK)) (reg 3)) DK) 3

@[expose] noncomputable def wK (w : List Int) : Nat × Nat :=
  (wFK c rm one A A B Bi w one, wSK c rm one A A B Bi w one)

@[expose] noncomputable def TK : Nat × Nat :=
  ppow (pm (pm (pm (pinv (wK (CFSG.Quasithin.H13.J4.Native.vLetters ())))
    (wK (CFSG.Quasithin.H13.J4.Native.uLetters ()))) (wK (CFSG.Quasithin.H13.J4.Native.vLetters ())))
    (wK (CFSG.Quasithin.H13.J4.Native.uLetters ()))) 22

@[expose] noncomputable def cnK (G E : Nat × Nat) (k : Nat) : Nat × Nat :=
  pm G (ppow (pm (pm (pm (pinv G) TK) G) E) k)

@[expose] noncomputable def conjK (k : Nat) : Nat × Nat :=
  pm (pm (pinv (cnK (pm (B, Bi) (A, A)) ZK k)) TK) (cnK (pm (B, Bi) (A, A)) ZK k)

theorem fuse : Nat.beq (conjK 3).1 ZK.1 = true := by quickRfl

theorem neg_fuse : notB (Nat.beq (conjK 2).1 ZK.1) = true := by quickRfl

end CertificateChecks.KernelJ4Count.Fuse

end

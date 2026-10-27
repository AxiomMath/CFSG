module

public import Certificates.Kernel.SporSch.Tits.Inv2266M
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelEvenBN

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch

@[expose] noncomputable def bitsK (M : Nat) (n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih i => Bool.rec (motive := fun _ => List Nat) (ih (Nat.succ i)) (i :: ih (Nat.succ i))
      (Nat.beq (Nat.land (Nat.shiftRight M i) 1) 1)) n

@[expose] noncomputable def CNtC : List Nat := bitsK TitsMN.M (tot5 TitsN.LR) 0

theorem mCNt : Nat.beq (maskOf CNtC) TitsMN.M = true := by quickRfl

theorem aCNt : ascK (tot5 TitsN.LR) CNtC 0 = true := by quickRfl

theorem lCNt : Nat.beq CNtC.length 1536 = true := by quickRfl

theorem negCNt : (Nat.beq (maskOf (CNtC.take 100)) TitsMN.M).not = true := by quickRfl

end CertificateChecks.KernelEvenBN

end

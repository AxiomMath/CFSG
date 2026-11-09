
module

public import Certificates.Data.Kernel.MonsterB.FischerBT
public import CFSG.Monster.B.TwoA.Fischer.CertBin
public import CFSG.Monster.B.TwoA.Fischer.CertData
public import Certificates.Data.Kernel.MonsterB.FischerK
public import Certificates.Kernel.MonsterB.FischerData3067

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.KC.FischerK
  CFSG.KC.FischerB CFSG.KLie.CT

@[expose] noncomputable def loopB {β : Type} (n : Nat) (g : Nat → β → β) (b : β) : β :=
  Nat.rec (motive := fun _ => Nat → β → β) (fun _ b => b) (fun _ ih i b => ih (Nat.succ i) (g i b))
    n 0 b

@[expose] noncomputable def rowB (k : Nat) : List Nat := List.take 11 (fColArr[k]!).toList

@[expose] noncomputable def mulB (k u : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (vecMulL (fColArr[k]!).toList u) (vecMulL (rowB k) u)
    (Nat.blt u 2048)

abbrev SKB := BT × BT × BT × BT × List Nat × Nat

@[expose] noncomputable def stepKB (t u k : Nat) (S : SKB) : SKB :=
  Bool.rec (motive := fun _ => SKB) S
    (setT S.1 (mulB k u) t, setT S.2.1 (mulB k u) (Nat.succ (getT S.2.1 u)),
      setT S.2.2.1 (mulB k u) u, setT S.2.2.2.1 (mulB k u) k, mulB k u :: S.2.2.2.2.1,
      Nat.succ S.2.2.2.2.2)
    (Bool.rec (motive := fun _ => Bool) false (Nat.beq (getT S.1 (mulB k u)) 2048)
      (Nat.blt (mulB k u) 2048))

abbrev SHB := BT × BT × BT × BT × List Nat × List Nat × Nat × Nat

@[expose] noncomputable def frontB (F B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.reverse B) (fun a l _ => a :: l) F

@[expose] noncomputable def backB (F B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ _ _ => B) F

@[expose] noncomputable def finHB (S : SHB) (R : SKB) : SHB :=
  (R.1, R.2.1, R.2.2.1, R.2.2.2.1, List.tail (frontB S.2.2.2.2.1 S.2.2.2.2.2.1),
    R.2.2.2.2.1, R.2.2.2.2.2, Nat.succ S.2.2.2.2.2.2.2)

@[expose] noncomputable def stepHB (t : Nat) (_ : Nat) (S : SHB) : SHB :=
  Bool.rec (motive := fun _ => SHB) S
    (finHB S (loopB 2 (stepKB t (List.headD (frontB S.2.2.2.2.1 S.2.2.2.2.2.1) 0))
      (S.1, S.2.1, S.2.2.1, S.2.2.2.1, backB S.2.2.2.2.1 S.2.2.2.2.2.1, S.2.2.2.2.2.2.1)))
    (Nat.blt S.2.2.2.2.2.2.2 S.2.2.2.2.2.2.1)

abbrev SOB := BT × BT × BT × BT × Nat

@[expose] noncomputable def finOB (t : Nat) (R : SHB) : SOB := (R.1, R.2.1, R.2.2.1, R.2.2.2.1, Nat.succ t)

@[expose] noncomputable def stepOB (s : Nat) (S : SOB) : SOB :=
  Bool.rec (motive := fun _ => SOB) S
    (finOB S.2.2.2.2 (loopB 2048 (stepHB S.2.2.2.2)
      (setT S.1 s S.2.2.2.2, S.2.1, S.2.2.1, S.2.2.2.1, [s], [], 1, 0)))
    (Nat.beq (getT S.1 s) 2048)

@[expose] noncomputable def orbRunB : SOB :=
  loopB 2048 stepOB (mkB 2048 11, mkB 0 11, mkB 0 11, mkB 0 11, 0)

@[expose] noncomputable def orbFinB (y : SOB) : BT × BT × BT × BT := (y.1, y.2.1, y.2.2.1, y.2.2.2.1)

@[expose] noncomputable def orbitDataB : BT × BT × BT × BT := orbFinB orbRunB

@[expose] noncomputable def orbChkB (D : BT × BT × BT × BT) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun a r => Prod.rec (motive := fun _ => Bool)
    (fun b r => Prod.rec (motive := fun _ => Bool) (fun c d =>
      allN 2048 fun m => getT a m == fget (FD.ORB[0]!) m 11 && getT b m == fget (FD.ORB[1]!) m 11 &&
        getT c m == fget (FD.ORB[2]!) m 11 && getT d m == fget (FD.ORB[3]!) m 11) r) r) D

end CertificateChecks.KernelMonB.F3067

end

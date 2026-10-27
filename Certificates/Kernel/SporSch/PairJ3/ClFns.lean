module

public import Certificates.Kernel.SporSch.PairJ3.ClData
public import CFSG.Certificates.Kernel.SporSch.PairClSound

public section

namespace CertificateChecks.KernelSporSch.PJ3Cl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def X : Nat → Nat := rowGet PJ3T.XT 92

@[expose] noncomputable def W : Nat → Nat := rowGet PJ3T.WT 40

@[expose] noncomputable def K : Nat → Nat := rowGet PJ3T.KT PJ3T.kw

@[expose] noncomputable def SO : Nat → Nat := rowGet PJ3T.ST 20

@[expose] noncomputable def SOI : Nat → Nat := rowGet PJ3T.SIT 20

@[expose] def gl (l : Nat) : Nat := l

@[expose] noncomputable def tsB (i : Nat) : Bool := Nat.beq (PJ3T.Ts i) (stepsAt 6156 13 PJ3.S 5 PJ3.BP i)

@[expose] noncomputable def ltB (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 6156 13 5 PJ3T.NR PJ3.S PJ3.SI PJ3T.LT) 1024

@[expose] noncomputable def ptB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 6156 13 PJ3T.NR PJ3.LR PJ3T.Ts PJ3T.PT i) 1024

@[expose] noncomputable def qtB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 6156 13 PJ3T.NR PJ3.LR PJ3T.QT i) 1024

@[expose] noncomputable def recB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (recOKT 6156 13 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT 4 CFSG.Sporadic.Schreier.PairJ3.bs
      (fun t => rcnt (PJ3.LR t)) X K PJ3T.c) 64

@[expose] noncomputable def srtB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (keySortAt [(PJ3T.c, K)] SO SOI PJ3T.c) 64

@[expose] noncomputable def runB (g r : Nat) : Bool :=
  Nat.beq (runNFT 6156 13 5 PJ3T.NR PJ3T.NR PJ3T.LT PJ3T.PT PJ3T.QT 4
    CFSG.Sporadic.Schreier.PairJ3.bs gl X W K 2 PJ3T.c 32
    (Nat.mul (Nat.add (Nat.mul g 8) r) 32) (PJ3T.C (Nat.add (Nat.mul g 8) r)))
    (PJ3T.C (Nat.succ (Nat.add (Nat.mul g 8) r)))

end CertificateChecks.KernelSporSch.PJ3Cl

end

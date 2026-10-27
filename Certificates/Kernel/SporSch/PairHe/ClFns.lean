module

public import Certificates.Kernel.SporSch.PairHe.ClDataA
public import Certificates.Kernel.SporSch.PairHe.ClDataB
public import Certificates.Kernel.SporSch.PairHe.ClDataJ
public import Certificates.Kernel.Sporadic.He.Chain2112
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Sporadic.Schreier.PairHeCheckInputs

public section

namespace CertificateChecks.KernelSporSch.PHeCl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] noncomputable def XA : Nat → Nat := rowGet PHeT.XT 108

@[expose] noncomputable def WA : Nat → Nat := rowGet PHeT.WT 40

@[expose] noncomputable def KA : Nat → Nat := rowGet PHeT.KT PHeT.kw

@[expose] noncomputable def SOA : Nat → Nat := rowGet PHeT.ST 20

@[expose] noncomputable def SOIA : Nat → Nat := rowGet PHeT.SIT 20

@[expose] noncomputable def XB : Nat → Nat := rowGet PHeU.XT 108

@[expose] noncomputable def WB : Nat → Nat := rowGet PHeU.WT 40

@[expose] noncomputable def KB : Nat → Nat := rowGet PHeU.KT PHeU.kw

@[expose] noncomputable def SOB : Nat → Nat := rowGet PHeU.ST 20

@[expose] noncomputable def SOIB : Nat → Nat := rowGet PHeU.SIT 20

@[expose] noncomputable def JSO : Nat → Nat := rowGet PHeJ.ST 20

@[expose] noncomputable def JSOI : Nat → Nat := rowGet PHeJ.SIT 20

@[expose] def gl (l : Nat) : Nat := l

@[expose] noncomputable def RPA : List Nat := [HeC.S 0]

@[expose] noncomputable def RPB : List Nat :=
  [HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 0, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 0,
    HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 0, HeC.S 1, HeC.S 1, HeC.S 1, HeC.S 0]

@[expose] noncomputable def tsB (i : Nat) : Bool :=
  Nat.beq (PHeT.Ts i) (stepsAt 8330 14 HeC.S 9 HeC.BP i)

@[expose] noncomputable def ltB (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 8330 14 9 PHeT.NR HeC.S HeC.SI PHeT.LT) 1024

@[expose] noncomputable def ptB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 8330 14 PHeT.NR HeC.LR PHeT.Ts PHeT.PT i) 1024

@[expose] noncomputable def qtB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 8330 14 PHeT.NR HeC.LR PHeT.QT i) 1024

@[expose] noncomputable def recA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (recOKT 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5 CFSG.Sporadic.Schreier.PairHe.bs
      (fun t => rcnt (HeC.LR t)) XA KA PHeT.c) 64

@[expose] noncomputable def srtA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (keySortAt [(PHeT.c, KA)] SOA SOIA PHeT.c) 64

@[expose] noncomputable def runA (g r : Nat) : Bool :=
  Nat.beq (runNFT 8330 14 9 PHeT.NR PHeT.NR PHeT.LT PHeT.PT PHeT.QT 5
    CFSG.Sporadic.Schreier.PairHe.bs gl XA WA KA 2 PHeT.c 32
    (Nat.mul (Nat.add (Nat.mul g 8) r) 32) (PHeT.C (Nat.add (Nat.mul g 8) r)))
    (PHeT.C (Nat.succ (Nat.add (Nat.mul g 8) r)))

@[expose] noncomputable def recB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (recOKT 8330 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5 CFSG.Sporadic.Schreier.PairHe.bs
      (fun t => rcnt (HeC.LR t)) XB KB PHeU.c) 64

@[expose] noncomputable def srtB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (keySortAt [(PHeU.c, KB)] SOB SOIB PHeU.c) 64

@[expose] noncomputable def runB (g r : Nat) : Bool :=
  Nat.beq (runNFT 8330 14 9 PHeT.NR PHeT.NR PHeT.LT PHeT.PT PHeT.QT 5
    CFSG.Sporadic.Schreier.PairHe.bs gl XB WB KB 2 PHeU.c 32
    (Nat.mul (Nat.add (Nat.mul g 8) r) 32) (PHeU.C (Nat.add (Nat.mul g 8) r)))
    (PHeU.C (Nat.succ (Nat.add (Nat.mul g 8) r)))

@[expose] noncomputable def jsrt (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (keySortAt [(PHeT.c, KA), (PHeU.c, KB)] JSO JSOI (Nat.add PHeT.c PHeU.c)) 64

end CertificateChecks.KernelSporSch.PHeCl

end

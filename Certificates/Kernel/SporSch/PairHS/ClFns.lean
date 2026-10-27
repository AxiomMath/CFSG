module

public import Certificates.Kernel.SporSch.PairHS.ClData
public import Certificates.Kernel.SporSch.PairJ3.GenClT
public import Certificates.Data.Kernel.SporSch.PairClT
public import CFSG.Certificates.Kernel.SporSch.PairClSound
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Certificates.Kernel.SporSch.PairKSound

public section

namespace CertificateChecks.KernelSporSch.PHSCl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch

@[expose] noncomputable def XA : Nat → Nat := rowGet PHST.XT 92

@[expose] noncomputable def WA : Nat → Nat := rowGet PHST.WT 40

@[expose] noncomputable def KA : Nat → Nat := rowGet PHST.KT PHST.kw

@[expose] noncomputable def SOA : Nat → Nat := rowGet PHST.ST 20

@[expose] noncomputable def SOIA : Nat → Nat := rowGet PHST.SIT 20

@[expose] noncomputable def XB : Nat → Nat := rowGet PHSU.XT 92

@[expose] noncomputable def WB : Nat → Nat := rowGet PHSU.WT 40

@[expose] noncomputable def KB : Nat → Nat := rowGet PHSU.KT PHSU.kw

@[expose] noncomputable def SOB : Nat → Nat := rowGet PHSU.ST 20

@[expose] noncomputable def SOIB : Nat → Nat := rowGet PHSU.SIT 20

@[expose] noncomputable def JSO : Nat → Nat := rowGet PHSJ.ST 20

@[expose] noncomputable def JSOI : Nat → Nat := rowGet PHSJ.SIT 20

@[expose] def gl (l : Nat) : Nat := l

@[expose] noncomputable def RPA : List Nat := [PHSC.S 0]

@[expose] noncomputable def RPB : List Nat :=
  [PHSC.S 1, PHSC.S 1, PHSC.S 0, PHSC.S 1, PHSC.S 1, PHSC.S 0, PHSC.S 1, PHSC.S 1, PHSC.S 0,
    PHSC.S 1, PHSC.S 1, PHSC.S 0, PHSC.S 1, PHSC.S 1, PHSC.S 0]

@[expose] noncomputable def tsB (i : Nat) : Bool :=
  Nat.beq (PHST.Ts i) (stepsAt 3850 12 PHSC.S 8 PHSC.BP i)

@[expose] noncomputable def ltB (s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ltOKT 3850 12 8 PHST.NR PHSC.S PHSC.SI PHST.LT) 1024

@[expose] noncomputable def ptB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (ptOKT 3850 12 PHST.NR PHSC.LR PHST.Ts PHST.PT i) 1024

@[expose] noncomputable def qtB (i s : Nat) : Bool :=
  allBlk (Nat.mul s 1024) (qtOKT 3850 12 PHST.NR PHSC.LR PHST.QT i) 1024

@[expose] noncomputable def recA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (recOKT 3850 12 PHST.NR PHST.NR PHST.LT PHST.PT 4 CFSG.Sporadic.Schreier.PairHS.bs
      (fun t => rcnt (PHSC.LR t)) XA KA PHST.c) 64

@[expose] noncomputable def srtA (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (keySortAt [(PHST.c, KA)] SOA SOIA PHST.c) 64

@[expose] noncomputable def runA (g r : Nat) : Bool :=
  Nat.beq (runNFT 3850 12 8 PHST.NR PHST.NR PHST.LT PHST.PT PHST.QT 4
    CFSG.Sporadic.Schreier.PairHS.bs gl XA WA KA 2 PHST.c 32
    (Nat.mul (Nat.add (Nat.mul g 8) r) 32) (PHST.C (Nat.add (Nat.mul g 8) r)))
    (PHST.C (Nat.succ (Nat.add (Nat.mul g 8) r)))

@[expose] noncomputable def recB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (recOKT 3850 12 PHST.NR PHST.NR PHST.LT PHST.PT 4 CFSG.Sporadic.Schreier.PairHS.bs
      (fun t => rcnt (PHSC.LR t)) XB KB PHSU.c) 64

@[expose] noncomputable def srtB (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64) (keySortAt [(PHSU.c, KB)] SOB SOIB PHSU.c) 64

@[expose] noncomputable def runB (g r : Nat) : Bool :=
  Nat.beq (runNFT 3850 12 8 PHST.NR PHST.NR PHST.LT PHST.PT PHST.QT 4
    CFSG.Sporadic.Schreier.PairHS.bs gl XB WB KB 2 PHSU.c 32
    (Nat.mul (Nat.add (Nat.mul g 8) r) 32) (PHSU.C (Nat.add (Nat.mul g 8) r)))
    (PHSU.C (Nat.succ (Nat.add (Nat.mul g 8) r)))

@[expose] noncomputable def jsrt (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) 64)
    (keySortAt [(PHST.c, KA), (PHSU.c, KB)] JSO JSOI (Nat.add PHST.c PHSU.c)) 64

end CertificateChecks.KernelSporSch.PHSCl

end

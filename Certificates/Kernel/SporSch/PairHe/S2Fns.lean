module

public import Certificates.Kernel.SporSch.PairHe.S2Data
public import Certificates.Kernel.SporSch.PairHe.ClFns
public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CertificateChecks.KernelSporSch.PHeSn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor

@[expose] def bs : List Nat := CFSG.Sporadic.Schreier.PairHe.bs

@[expose] noncomputable def nfp (F x : Nat) : Nat := nfPtT 14 PHeT.NR PHeT.NR PHeT.LT PHeT.PT 5 F x

@[expose] noncomputable def wordP (RP : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun P _ ih x => ih (pg 14 (mask 14) P x)) RP x

@[expose] noncomputable def tAP (x : Nat) : Nat := pg 14 (mask 14) (HeC.S 0) x

@[expose] noncomputable def tBP (x : Nat) : Nat := wordP PHeCl.RPB x

@[expose] noncomputable def r2 (i : Nat) : Nat := rowGet PHeS.R2 80 i

@[expose] noncomputable def par2 (i : Nat) : Nat := Nat.mod (rowGet PHeS.P2 16 i) 4096

@[expose] noncomputable def lab2 (i : Nat) : Nat := Nat.div (rowGet PHeS.P2 16 i) 4096

@[expose] noncomputable def gr2 (l : Nat) : Nat := PHeS.G2 l

@[expose] noncomputable def m2 (i l : Nat) : Nat := rowGet PHeS.M2 12 (Nat.add (Nat.mul i 5) l)

@[expose] noncomputable def d2 (i : Nat) : Nat := rowGet PHeS.D2 80 i

@[expose] noncomputable def c2 (i : Nat) : Nat := rowGet PHeS.C2 2 i

@[expose] noncomputable def tSel (c x : Nat) : Nat := nIf(Nat.beq c 0, tAP x, tBP x)

@[expose] noncomputable def K2 (i : Nat) : Nat := keyL 8330 (nfp (r2 i)) bs

@[expose] noncomputable def s2At (i : Nat) : Bool :=
  bAnd(nfValidK 5 HeC.LR (r2 i),
  bAnd(bIf(Nat.blt 0 i, bAnd(Nat.blt (par2 i) i, bAnd(Nat.blt (lab2 i) 5,
      eqOnL bs (nfp (r2 i)) (fun b => nfp (r2 (par2 i)) (nfp (r2 (gr2 (lab2 i))) b)))),
    eqOnL bs (nfp (r2 i)) (fun x => x)),
  bAnd(allN 5 (fun l => bAnd(Nat.blt (m2 i l) 1024,
    eqOnL bs (fun b => nfp (r2 i) (nfp (r2 (gr2 l)) b)) (nfp (r2 (m2 i l))))),
  bIf(ordPL bs (nfp (r2 i)) 2, bAnd(nfValidK 5 HeC.LR (d2 i),
    eqOnL bs (fun b => nfp (d2 i) (tSel (c2 i) b)) (fun b => nfp (r2 i) (nfp (d2 i) b))), true))))

@[expose] noncomputable def s2B (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) (nat_lit 16)) s2At (nat_lit 16)

@[expose] noncomputable def srt2 (g r : Nat) : Bool :=
  allBlk (Nat.mul (Nat.add (Nat.mul g 8) r) (nat_lit 16))
    (keySortAt [(1024, K2)] (rowGet PHeS.O2 12) (rowGet PHeS.OI2 12) 1024) (nat_lit 16)

@[expose] noncomputable def gensB : Bool := allN 5 (fun l => Nat.blt (gr2 l) 1024)

end CertificateChecks.KernelSporSch.PHeSn

end

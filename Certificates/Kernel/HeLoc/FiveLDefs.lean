module

public import Certificates.Kernel.HeLoc.FiveLData
public import Certificates.Kernel.HeLoc.FiveC0
public import Certificates.Kernel.HeLoc.MemDefs

public section

namespace CertificateChecks.KernelHeLoc.FiveL

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def A (k : Nat) : Nat := Five.FH.F k

@[expose] noncomputable def AI (k : Nat) : Nat := AI5 k

@[expose] noncomputable def pa (k x : Nat) : Nat := pg 14 (mask 14) (A k) x

@[expose] noncomputable def pi (k x : Nat) : Nat := pg 14 (mask 14) (AI k) x

@[expose] noncomputable def ln (j x : Nat) : Nat := pa (Nat.add 2 j) (pa 8 (pi (Nat.add 2 j) x))

@[expose] noncomputable def QE (i k : Nat) : Nat := fld(Q.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def qv (i x : Nat) : Nat := trV pa Q.P Q.L 25 i x

@[expose] noncomputable def qkey (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heFiveKeys (qv i)

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def memI (i : Nat) : Bool :=
  memB (A (i / 10)) (NF5.getD (i / 10) 0) (FL5.getD (i / 10) 0) (i % 10)

@[expose] noncomputable def coverAt (k : Nat) : Bool :=
  strictB (QW.getD k 0) fun w => bIf(Nat.beq w 0, eqOnL Five.bs (qv k) (fun x => x),
    bAnd(Nat.blt (Nat.div w 8) 6, bAnd(Nat.blt 0 (Nat.mod w 8), bAnd(Nat.blt (Nat.mod w 8) 5,
      eqOnL Five.bs (qv k) (powF (ln (Nat.div w 8)) (Nat.mod w 8))))))

@[expose] noncomputable def distAt (j j' : Nat) : Bool :=
  bIf(Nat.beq j j', true, allN 5 fun e => !eqOnL Five.bs (ln j) (powF (ln j') e))

@[expose] noncomputable def lineAt (j : Nat) : Bool :=
  bAnd(eqOnL Five.bs (powF (ln j) 5) (fun x => x), bAnd(!eqOnL Five.bs (ln j) (fun x => x),
    bAnd(Nat.blt (LQ.getD j 0) 25, eqOnL Five.bs (qv (LQ.getD j 0)) (ln j))))

end CertificateChecks.KernelHeLoc.FiveL

end

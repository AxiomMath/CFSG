module

public import Certificates.Kernel.HeLoc.SevenData
public import Certificates.Kernel.HeLoc.MemDefs
public import Certificates.Data.Kernel.HeLoc.Tree

public section

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def A (k : Nat) : Nat := SH.F k

@[expose] noncomputable def AI (k : Nat) : Nat := SI k

@[expose] noncomputable def pa (k x : Nat) : Nat := pg 14 (mask 14) (A k) x

@[expose] noncomputable def pi (k x : Nat) : Nat := pg 14 (mask 14) (AI k) x

@[expose] def repIx (i : Nat) : Nat := nIf(Nat.beq i 0, 59, nIf(Nat.beq i 1, 65, 70))

@[expose] noncomputable def rc (j : Nat) : Nat := Nat.mod (CFSG.RankThree.PartOne.heSevenRec.getD j 0) 3

@[expose] noncomputable def ln (j x : Nat) : Nat :=
  pa (Nat.add 2 j) (pa (repIx (rc j)) (pi (Nat.add 2 j) x))

@[expose] def bs : List Nat := [0, 1, 2, 3, 4]

@[expose] noncomputable def QE (i k : Nat) : Nat := fld(Q.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def qv (i x : Nat) : Nat := trV pa Q.P Q.L 343 i x

@[expose] noncomputable def qkey (i : Nat) : Nat :=
  keyV 8330 CFSG.RankThree.PartOne.heSevenKeys (qv i)

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def memI (i : Nat) : Bool :=
  memB (A (i / 10)) (NF.getD (i / 10) 0) (FL.getD (i / 10) 0) (i % 10)

@[expose] noncomputable def coverAt (k : Nat) : Bool :=
  strictB (QW.getD k 0) fun w => bIf(Nat.beq w 0, eqOnL bs (qv k) (fun x => x),
    bAnd(Nat.blt (Nat.div w 8) 57, bAnd(Nat.blt 0 (Nat.mod w 8), bAnd(Nat.blt (Nat.mod w 8) 7,
      eqOnL bs (qv k) (powF (ln (Nat.div w 8)) (Nat.mod w 8))))))

@[expose] noncomputable def distAt (j j' : Nat) : Bool :=
  bIf(Nat.beq j j', true, CFSG.KC.Enum.allN 7 fun e => !eqOnL bs (ln j) (powF (ln j') e))

@[expose] noncomputable def lineAt (j : Nat) : Bool :=
  bAnd(eqOnL bs (powF (ln j) 7) (fun x => x), bAnd(!eqOnL bs (ln j) (fun x => x),
    bAnd(Nat.blt (LQ.getD j 0) 343, eqOnL bs (qv (LQ.getD j 0)) (ln j))))

end CertificateChecks.KernelHeLoc.Seven

end

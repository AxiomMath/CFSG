module

public import Certificates.Kernel.Om1K.Data

public section

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum CFSG.KC.SetOrb CFSG.KS
open CertificateChecks.KernelOm2 (pc2)

@[expose] noncomputable def inSub (N : Nat) (X Y : Nat → Nat) (j : Nat) : Bool :=
  Nat.blt (Y j) N && Nat.beq (X (Y j)) j

@[expose] noncomputable def covK (j : Nat) : Bool :=
  Nat.beq j 0 || Nat.beq (imgK 8 24 (EL.G 4) (Orb.C 0)) (Orb.M j) ||
    inSub Sub.c0.N Sub.c0.X Sub.c0.Y j || inSub Sub.c1.N Sub.c1.X Sub.c1.Y j ||
    inSub Sub.c2.N Sub.c2.X Sub.c2.Y j || inSub Sub.c3.N Sub.c3.X Sub.c3.Y j ||
    inSub Sub.c4.N Sub.c4.X Sub.c4.Y j || inSub Sub.c5.N Sub.c5.X Sub.c5.Y j ||
    inSub Sub.c6.N Sub.c6.X Sub.c6.Y j || inSub Sub.c7.N Sub.c7.X Sub.c7.Y j

@[expose] noncomputable def orbOK (i : Nat) : Bool :=
  bAnd(codeOK 240 8 24 (Orb.C i) (Orb.M i),
  bAnd(closK 8 24 7 3150 XG.G Orb.C Orb.M (fun j => j) Orb.E i,
  bAnd(treeK 8 24 7 XG.G Orb.C Orb.M (fun j => j) Orb.D i, covK i)))

@[expose] noncomputable def orbOKc (c : Nat) : Bool :=
  allN 50 fun d => orbOK (Nat.add (Nat.mul 50 c) d)

@[expose] noncomputable def tgR (R k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) R (TG.G k) (Nat.blt k 7)

@[expose] noncomputable def subOK (N : Nat) (X D : Nat → Nat) (R : Nat) : Bool :=
  bAnd(allN N (treeK 8 24 7 TG.G Orb.C Orb.M X D),
  bAnd(allN N (fun i => Nat.blt (X i) 3150),
    Nat.beq (imgK 8 24 R (Orb.C 0)) (Orb.M (X 0))))

@[expose] noncomputable def transOK (N : Nat) (X Y D : Nat → Nat) (R : Nat) : Bool :=
  bAnd(allN N (treeK 8 24 8 (tgR R) Orb.C Orb.M X D),
  bAnd(allN N (fun i => bAnd(invK X Y i, Nat.blt (X i) 3150)), Nat.beq (X 0) 0))

@[expose] noncomputable def oaOK (i : Nat) : Bool :=
  bAnd(codeOK 240 8 4 (OA.C i) (OA.M i), treeK 8 4 7 XG.G OA.C OA.M (fun j => j) OA.D i)

@[expose] noncomputable def oaOKc (c : Nat) : Bool :=
  allN 60 fun d => oaOK (Nat.add (Nat.mul 60 c) d)

@[expose] noncomputable def roOK (i : Nat) : Bool :=
  bAnd(codeOK 240 8 1 (RO.C i) (RO.M i), treeK 8 1 7 XG.G RO.C RO.M (fun j => j) RO.D i)

@[expose] noncomputable def ttOK (p : Nat) : Bool :=
  bIf(Nat.beq p 0, bAnd(Nat.beq (TT.G 0) (CFSG.KC.Enum.pidn 240 8),
      Nat.beq (TI.G 0) (CFSG.KC.Enum.pidn 240 8)),
    bAnd(Nat.beq (TT.G p) (pc2 (XG.G (Nat.div (RO.D p) 65536)) (TT.G (Nat.mod (RO.D p) 65536))),
      Nat.beq (TI.G p) (pc2 (TI.G (Nat.mod (RO.D p) 65536)) (XI.G (Nat.div (RO.D p) 65536)))))

@[expose] noncomputable def rootK : Nat := pg 8 (mask 8) (RO.C 0) 0

@[expose] noncomputable def sgOK (j : Nat) : Bool :=
  strictB (pg 8 (mask 8) (IX.G j) 0) fun q => strictB (pg 8 (mask 8) (IX.G j) 1) fun k =>
    strictB (pg 8 (mask 8) (IX.G j) 2) fun p =>
      bAnd(Nat.blt q 240, bAnd(Nat.blt k 7, bAnd(Nat.blt p 240,
      bAnd(Nat.beq (SG.G j) (pc2 (TI.G q) (pc2 (XG.G k) (TT.G p))),
        Nat.beq (pg 8 (mask 8) (SG.G j) rootK) rootK))))

@[expose] noncomputable def ocOK (i : Nat) : Bool :=
  bAnd(codeOK 240 8 8 (OC.C i) (OC.M i), treeK 8 8 10 SG.G OC.C OC.M (fun j => j) OC.D i)

@[expose] noncomputable def ocOKc (c : Nat) : Bool :=
  allN 60 fun d => ocOK (Nat.add (Nat.mul 60 c) d)

end CertificateChecks.KernelOm1.A

end

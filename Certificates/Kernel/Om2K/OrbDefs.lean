module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import Certificates.Data.Kernel.SetOrb
public import Certificates.Kernel.Om2K.OrbData

public section

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum CFSG.KC.SetOrb

@[expose] noncomputable def orbOK (i : Nat) : Bool :=
  bAnd(codeOK 480 9 48 (Orb.C i) (Orb.M i),
  bAnd(closK 9 48 8 6300 L.G Orb.C Orb.M (fun j => j) Orb.E i,
    treeK 9 48 8 L.G Orb.C Orb.M (fun j => j) Orb.D i))

@[expose] noncomputable def tgR (R k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) R (TG.G k) (Nat.blt k 8)

@[expose] noncomputable def subOK (N : Nat) (X Y E D : Nat → Nat) (R : Nat) : Bool :=
  bAnd(allN N (closK 9 48 8 N TG.G Orb.C Orb.M X E),
  bAnd(allN N (treeK 9 48 8 TG.G Orb.C Orb.M X D),
  bAnd(allN N (fun i => bAnd(invK X Y i, Nat.blt (X i) 6300)),
    Nat.beq (imgK 9 48 R (Orb.C 0)) (Orb.M (X 0)))))

@[expose] noncomputable def transOK (N : Nat) (X Y E D : Nat → Nat) (R : Nat) : Bool :=
  bAnd(allN N (closK 9 48 9 N (tgR R) Orb.C Orb.M X E),
  bAnd(allN N (treeK 9 48 9 (tgR R) Orb.C Orb.M X D),
  bAnd(allN N (fun i => bAnd(invK X Y i, Nat.blt (X i) 6300)), Nat.beq (X 0) 0)))

@[expose] noncomputable def inSub (N : Nat) (X Y : Nat → Nat) (j : Nat) : Bool :=
  Nat.blt (Y j) N && Nat.beq (X (Y j)) j

@[expose] noncomputable def covK (j : Nat) : Bool :=
  Nat.beq j 0 || (List.range 3).any (fun k => Nat.beq (imgK 9 48 (FU.G k) (Orb.C 0)) (Orb.M j)) ||
    inSub Sub.c0.N Sub.c0.X Sub.c0.Y j || inSub Sub.c1.N Sub.c1.X Sub.c1.Y j ||
    inSub Sub.c2.N Sub.c2.X Sub.c2.Y j || inSub Sub.c3.N Sub.c3.X Sub.c3.Y j ||
    inSub Sub.c4.N Sub.c4.X Sub.c4.Y j || inSub Sub.c5.N Sub.c5.X Sub.c5.Y j ||
    inSub Sub.c6.N Sub.c6.X Sub.c6.Y j || inSub Sub.c7.N Sub.c7.X Sub.c7.Y j ||
    inSub Sub.c8.N Sub.c8.X Sub.c8.Y j || inSub Sub.c9.N Sub.c9.X Sub.c9.Y j ||
    inSub Sub.c10.N Sub.c10.X Sub.c10.Y j || inSub Sub.c11.N Sub.c11.X Sub.c11.Y j

@[expose] noncomputable def orbOKc (c : Nat) : Bool :=
  allN 100 fun d => orbOK (Nat.add (Nat.mul 100 c) d)

end CertificateChecks.KernelOm2

end

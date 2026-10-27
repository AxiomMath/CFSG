module

public import Certificates.Data.Kernel.ONOutK3.Mat
public import Certificates.Kernel.ONOutK3.MatData
public import Certificates.Kernel.ONOutK3.Defs
public import Certificates.Kernel.Sporadic.ON.Span
public import Certificates.Data.GrSLitL34FactsCF23ONOutK1Data

public section

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.KC.Ord

@[expose] noncomputable def KK (x : Nat) : Nat := CFSG.KS.ON.key CertificateChecks.KernelSpor.ONV.K x

@[expose] noncomputable def SPf (t : Nat) : Nat := List.getD CertificateChecks.KernelSpor.ON.SP t (nat_lit 0)

@[expose] noncomputable def sM (MD : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0), MD (Nat.add (nat_lit 1) (Nat.div c (nat_lit 2))),
    MD (Nat.add (nat_lit 8) (Nat.div c (nat_lit 2))))

@[expose] noncomputable def gM (MD : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0), MD (Nat.add (nat_lit 15) (Nat.div c (nat_lit 2))),
    MD (Nat.add (nat_lit 22) (Nat.div c (nat_lit 2))))

@[expose] noncomputable def hM (MD : Nat → Nat) (a : Nat) : Nat := MD (Nat.add (nat_lit 29) a)

@[expose] noncomputable def mchkG (MD : Nat → Nat) (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 0), consts3OK (nat_lit 154) (nat_lit 9) (nat_lit 23716) LO RM CI ONE UP,
  bIf(Nat.beq c (nat_lit 1), allN (nat_lit 32) (fun i => VLD (MD i)),
  bIf(Nat.beq c (nat_lit 2), Nat.beq (MUL (rowsK fun t => KK (SPf t)) (MD (nat_lit 0))) ONE,
  bIf(Nat.blt c (nat_lit 10), Nat.beq (MD (Nat.sub c (nat_lit 2)))
      (matT KK SPf (MD (nat_lit 0)) (CertificateChecks.KernelSpor.ON.TT (Nat.sub c (nat_lit 3)))),
  bIf(Nat.blt c (nat_lit 17), Nat.beq (MD (Nat.sub c (nat_lit 2)))
      (matT KK SPf (MD (nat_lit 0)) (CertificateChecks.KernelSpor.ON.UU (Nat.sub c (nat_lit 10)))),
  bIf(Nat.blt c (nat_lit 20), Nat.beq (MD (Nat.add c (nat_lit 12)))
      (matT KK SPf (MD (nat_lit 0)) (CertificateChecks.KernelSpor.ON3.mG (Nat.sub c (nat_lit 17)))),
  bIf(Nat.beq c (nat_lit 20),
    Nat.beq (MD (nat_lit 15)) (wordT (sM MD) CFSG.ComponentClassification.SolMax.ONOut.wA),
  bIf(Nat.beq c (nat_lit 21),
    Nat.beq (MD (nat_lit 16)) (wordT (sM MD) CFSG.ComponentClassification.SolMax.ONOut.wB),
  bIf(Nat.blt c (nat_lit 27), Nat.beq (MD (Nat.sub c (nat_lit 5)))
      (wordT (gM MD) CFSG.ONSchreier.Data.strongWords[Nat.sub c (nat_lit 20)]!),
  bIf(Nat.blt c (nat_lit 34), Nat.beq (MUL (MD (Nat.sub c (nat_lit 12))) (MD (Nat.sub c (nat_lit 5)))) ONE,
    Nat.beq (wordT (gM MD) CFSG.ONSchreier.Data.MWords[Nat.sub c (nat_lit 34)]!)
      (uT (hM MD) (UL (Nat.sub c (nat_lit 34))) (UW (Nat.sub c (nat_lit 34))) ONE)))))))))))

@[expose] noncomputable def mchk (c : Nat) : Bool := mchkG ONK3M c

end CertificateChecks.KernelSpor.ONK3

end

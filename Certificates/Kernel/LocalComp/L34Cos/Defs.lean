module

public import Certificates.Kernel.LocalComp.L34Cos.Data

public section

namespace CertificateChecks.KernelLC.L34Cos

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def OT (s j : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), at8 T0 (nat_lit 252) j, nIf(Nat.beq s (nat_lit 1), at8 T1 (nat_lit 252) j,
  nIf(Nat.beq s (nat_lit 2), at8 T2 (nat_lit 252) j, nIf(Nat.beq s (nat_lit 3), at8 T3 (nat_lit 252) j,
  nIf(Nat.beq s (nat_lit 4), at8 T4 (nat_lit 252) j, nIf(Nat.beq s (nat_lit 5), at8 T5 (nat_lit 252) j,
  nIf(Nat.beq s (nat_lit 6), at8 T6 (nat_lit 252) j, at8 T7 (nat_lit 252) j)))))))

@[expose] noncomputable def OE (s j : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), at16 E0 (nat_lit 33) j, nIf(Nat.beq s (nat_lit 1), at16 E1 (nat_lit 33) j,
  nIf(Nat.beq s (nat_lit 2), at16 E2 (nat_lit 33) j, nIf(Nat.beq s (nat_lit 3), at16 E3 (nat_lit 33) j,
  nIf(Nat.beq s (nat_lit 4), at16 E4 (nat_lit 33) j, nIf(Nat.beq s (nat_lit 5), at16 E5 (nat_lit 33) j,
  nIf(Nat.beq s (nat_lit 6), at16 E6 (nat_lit 33) j, at16 E7 (nat_lit 33) j)))))))

@[expose] noncomputable def OS (s j : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), at16 S0 (nat_lit 18) j, nIf(Nat.beq s (nat_lit 1), at16 S1 (nat_lit 18) j,
  nIf(Nat.beq s (nat_lit 2), at16 S2 (nat_lit 18) j, nIf(Nat.beq s (nat_lit 3), at16 S3 (nat_lit 18) j,
  nIf(Nat.beq s (nat_lit 4), at16 S4 (nat_lit 18) j, nIf(Nat.beq s (nat_lit 5), at16 S5 (nat_lit 18) j,
  nIf(Nat.beq s (nat_lit 6), at16 S6 (nat_lit 18) j, at16 S7 (nat_lit 18) j)))))))

@[expose] noncomputable def OSI (s j : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), at16 SI0 (nat_lit 18) j, nIf(Nat.beq s (nat_lit 1), at16 SI1 (nat_lit 18) j,
  nIf(Nat.beq s (nat_lit 2), at16 SI2 (nat_lit 18) j, nIf(Nat.beq s (nat_lit 3), at16 SI3 (nat_lit 18) j,
  nIf(Nat.beq s (nat_lit 4), at16 SI4 (nat_lit 18) j, nIf(Nat.beq s (nat_lit 5), at16 SI5 (nat_lit 18) j,
  nIf(Nat.beq s (nat_lit 6), at16 SI6 (nat_lit 18) j, at16 SI7 (nat_lit 18) j)))))))

@[expose] noncomputable def ON (s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), nat_lit 315, nIf(Nat.blt s (nat_lit 4), nat_lit 120,
    nIf(Nat.blt s (nat_lit 7), nat_lit 336, nat_lit 280)))

@[expose] noncomputable def W (o j : Nat) : Nat :=
  nIf(Nat.beq o (nat_lit 0), at16 W0 (nat_lit 16) j, nIf(Nat.beq o (nat_lit 1), at16 W1 (nat_lit 16) j,
  nIf(Nat.beq o (nat_lit 2), at16 W2 (nat_lit 16) j, at16 W3 (nat_lit 16) j)))

@[expose] noncomputable def cj4 (x : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34R.G 3) x) (GI 3)

@[expose] noncomputable def cj44 (x : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (L34R.G 3) (L34R.G 3)) x)
    (pcomp 42 6 (mask 6) (GI 3) (GI 3))

@[expose] noncomputable def repK (s : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), RP 0, nIf(Nat.beq s (nat_lit 1), L34R.G 4,
  nIf(Nat.beq s (nat_lit 2), cj4 (L34R.G 4), nIf(Nat.beq s (nat_lit 3), cj44 (L34R.G 4),
  nIf(Nat.beq s (nat_lit 4), L34R.G 5, nIf(Nat.beq s (nat_lit 5), cj4 (L34R.G 5),
  nIf(Nat.beq s (nat_lit 6), cj44 (L34R.G 5), RP 3)))))))

@[expose] noncomputable def orbC (s : Nat) : Bool :=
  orbK 42 6 3 L34R.G GI (OT s) (OE s) (OS s) (OSI s) (ON s) 11 (RQ s)

@[expose] noncomputable def covC : Bool :=
  allN 4 fun o => allN (L34O.N o) fun j => strictB (W o j) fun v =>
    strictB (Nat.shiftRight v (nat_lit 9)) fun s => strictB (Nat.land v (nat_lit 511)) fun q =>
      andB (Nat.blt s (nat_lit 8)) (andB (Nat.blt q (ON s)) (Nat.beq (OT s q) (L34O.T o j)))

@[expose] noncomputable def sT (i : Nat) : Nat := at8 L34S.TP (nat_lit 252) i

@[expose] noncomputable def notRow (i : Nat) : Bool :=
  strictB (pinvS 42 6 (mask 6) (RQ i)) fun yi => allN 8 fun j =>
    orB (Nat.beq i j) (notInK 20160 sT (pcomp 42 6 (mask 6) yi (RQ j)))

end CertificateChecks.KernelLC.L34Cos

end

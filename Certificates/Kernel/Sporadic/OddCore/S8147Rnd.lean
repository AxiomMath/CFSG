module

public import Certificates.Kernel.Sporadic.OddCore.S2301Data
public import Certificates.Kernel.Sporadic.OddCore.S8147D
public import Certificates.Kernel.Sporadic.OddCore.S8147GD
public import Certificates.Kernel.Sporadic.OddCore.S8147Idx
public import Certificates.Data.Kernel.Suz2301

public section

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KD.S8147 CFSG.KC.S2301

@[expose] noncomputable def rnd (T k : Nat) : Bool :=
  bAnd(tabOK (nat_lit 1782) (K (Nat.sub k (nat_lit 1))) (X (Nat.sub k (nat_lit 1)))
      (Q (Nat.sub k (nat_lit 1))),
  bAnd(ordOK (nat_lit 1782) (Q (Nat.sub k (nat_lit 1))) (O (Nat.sub k (nat_lit 1))),
    roundOK (nat_lit 1782) (X (Nat.sub k (nat_lit 1))) (Q (Nat.sub k (nat_lit 1))) (X k) (Q k) T
      (O (Nat.sub k (nat_lit 1))) CFSG.KD.S2301.W))

@[expose] noncomputable def rnds (T k0 m : Nat) : Bool :=
  allN m fun j => rnd T (Nat.add k0 (Nat.add j (nat_lit 1)))

@[expose] noncomputable def ind (k p j : Nat) : Bool :=
  allN (nat_lit 1782) (indivOK (X (Nat.sub k (nat_lit 1))) (Q (Nat.sub k (nat_lit 1))) (X k) (Q k) p j)

@[expose] noncomputable def blkB (i s : Nat) : Bool :=
  strictB (CertificateChecks.KernelSpor.SFL12 i) fun T =>
    Nat.rec (motive := fun _ => Bool) (rnds T (caseStart i) (initLen i))
      (fun t _ => bAnd(ind (Nat.add (stageIdx i t) (nat_lit 1)) (point i t) t,
        rnds T (Nat.add (stageIdx i t) (nat_lit 1)) (rounds i t))) s

@[expose] noncomputable def caseB (i s : Nat) : Bool := bIf(Nat.ble s (nSteps i), blkB i s, true)

end CertificateChecks.KernelSpor.S8147

end

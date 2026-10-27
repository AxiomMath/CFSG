module

public import Certificates.Kernel.K133.GBarTwin

public section

namespace CertificateChecks.KernelK133

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 256 9 (mask 9) p q

@[expose] noncomputable def ap9 (X m : Nat) : Nat := pg 9 (mask 9) X m

@[expose] noncomputable def X (i : Nat) : Nat := GB.T i

@[expose] noncomputable def A (k : Nat) : Nat := X (GB.FI k)

@[expose] noncomputable def U (j : Nat) : Nat := X (GB.WI j)

@[expose] noncomputable def ncK (P Q : Nat) : Bool :=
  [1, 2, 4, 8, 16, 32, 64, 128].any fun e => !Nat.beq (ap9 P (ap9 Q e)) (ap9 Q (ap9 P e))

@[expose] noncomputable def lineK (k Q : Nat) : Bool :=
  Nat.beq Q (pidn 256 9) || Nat.beq Q (A k) || Nat.beq Q (GB.L2 k) || Nat.beq Q (GB.L3 k) ||
    Nat.beq Q (GB.L4 k)

@[expose] noncomputable def fzK (P : Nat) : Bool :=
  allN 256 fun m => Nat.beq m 0 || !Nat.beq (ap9 P m) m

@[expose] noncomputable def ffK (P Q : Nat) : Bool :=
  allN 256 fun m => Nat.beq m 0 || !(Nat.beq (ap9 P m) m && Nat.beq (ap9 Q m) m)

@[expose] noncomputable def coverK (i : Nat) : Bool :=
  ((Nat.blt (GB.P5 i) 624 && Nat.beq (GB.FI (GB.P5 i)) i) || Nat.beq (X i) (pidn 256 9) ||
    (Nat.blt (GB.Q5 i) 256 && !Nat.beq (ap9 (X i) (ap9 (X i) (ap9 (X i) (ap9 (X i)
      (ap9 (X i) (GB.Q5 i)))))) (GB.Q5 i))) &&
  ((Nat.blt (GB.P2 i) 475 && Nat.beq (GB.WI (GB.P2 i)) i) || Nat.beq (X i) (pidn 256 9) ||
    (Nat.blt (GB.Q2 i) 256 && !Nat.beq (ap9 (X i) (ap9 (X i) (GB.Q2 i))) (GB.Q2 i)))

@[expose] noncomputable def powK (k : Nat) : Bool :=
  Nat.blt (GB.FI k) GB.N && Nat.beq (GB.L2 k) (pc (A k) (A k)) &&
    Nat.beq (GB.L3 k) (pc (A k) (GB.L2 k)) && Nat.beq (GB.L4 k) (pc (A k) (GB.L3 k))

@[expose] noncomputable def pairB (k : Nat) : Bool :=
  fzK (A k) || allN 624 fun k' => ncK (A k) (A k') || lineK k (A k') || ffK (A k) (A k')

@[expose] noncomputable def inU (j k : Nat) : Bool :=
  !allBlk (GB.UO j) (fun t => !Nat.beq (GB.UV t) k) (GB.UO (j + 1) - GB.UO j)

@[expose] noncomputable def pairA (j : Nat) : Bool :=
  Nat.blt (GB.WI j) GB.N &&
  (allN 624 fun k => ncK (U j) (A k) || inU j k) &&
    allBlk (GB.UO j) (fun t => Nat.blt (GB.UV t) 624 && allBlk (GB.UO j) (fun t' =>
      ncK (A (GB.UV t)) (A (GB.UV t')) || lineK (GB.UV t) (A (GB.UV t')))
        (GB.UO (j + 1) - GB.UO j)) (GB.UO (j + 1) - GB.UO j)

end CertificateChecks.KernelK133

end

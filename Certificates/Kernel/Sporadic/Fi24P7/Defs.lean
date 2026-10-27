module

public import Certificates.Kernel.Sporadic.Fi24P7.Data

public section

namespace CFSG.KD.Fi24P7

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24P7

@[expose] noncomputable def okS (S K : List Nat) (c : Nat) : Bool :=
  Nat.beq (nIf(Nat.blt c (nat_lit 74),
      CFSG.KC.Fi24FixK.cntFix CFSG.KC.Fi24G2d.idN CFSG.KD.Fi24Fix.TG [] S (Nat.mul (nat_lit 4096) c)
        (nat_lit 4096) (nat_lit 64),
      CFSG.KC.Fi24FixK.cntFix CFSG.KC.Fi24G2d.idN CFSG.KD.Fi24Fix.TG [] S (nat_lit 303104)
        (nat_lit 3832) (nat_lit 64)))
    (CFSG.KC.Fi24Kn.nthN K c)

@[expose] noncomputable def chunk (f : Nat → Bool) (m c : Nat) : Bool :=
  allBelow (nat_lit 1024) (nat_lit 16) (fun t =>
    letB (Nat.add (Nat.mul (nat_lit 1024) c) t) (fun j => bIf(Nat.blt j m, f j, true)))

@[expose] noncomputable def ok0 (j : Nat) : Bool :=
  andB (incStep F0 (nat_lit 306936) (nat_lit 3159) j)
    (andB (wStep CFSG.KD.Fi24Fix.TG F0 PA0 J.A0 (nat_lit 3159) j)
      (andB (wStep CFSG.KD.Fi24Fix.TG F0 PB0 J.B0 (nat_lit 3159) j)
        (tStep PA0 PB0 PAR0 DEP0 (nat_lit 3159) (nat_lit 0) j)))

@[expose] noncomputable def ck0 (c : Nat) : Bool := chunk ok0 (nat_lit 3159) c

@[expose] noncomputable def pt2 (j : Nat) : Bool :=
  andB (incStep F2 (nat_lit 306936) (nat_lit 378) j)
    (andB (wStep CFSG.KD.Fi24Fix.TG F2 PA2 J.A2 (nat_lit 378) j)
      (wStep CFSG.KD.Fi24Fix.TG F2 PB2 B2 (nat_lit 378) j))

@[expose] noncomputable def pr2 (k : Nat) : Bool :=
  andB (qIncStep Q2 (nat_lit 378) (nat_lit 5670) k)
    (andB (qStep Q2 QA2 PA2 (nat_lit 378) (nat_lit 5670) k)
      (andB (qStep Q2 QB2 PB2 (nat_lit 378) (nat_lit 5670) k)
        (tStep QA2 QB2 QP2 QD2 (nat_lit 5670) (nat_lit 0) k)))

@[expose] noncomputable def cq2 (c : Nat) : Bool := chunk pr2 (nat_lit 5670) c

@[expose] noncomputable def pt4 (j : Nat) : Bool :=
  andB (incStep F4 (nat_lit 306936) (nat_lit 351) j)
    (andB (wStep CFSG.KD.Fi24Fix.TG F4 PA4 J.A4 (nat_lit 351) j)
      (wStep CFSG.KD.Fi24Fix.TG F4 PB4 J.B4 (nat_lit 351) j))

@[expose] noncomputable def pr4 (k : Nat) : Bool :=
  andB (qIncStep Q4 (nat_lit 351) (nat_lit 44226) k)
    (andB (qStep Q4 QA4 PA4 (nat_lit 351) (nat_lit 44226) k)
      (andB (qStep Q4 QB4 PB4 (nat_lit 351) (nat_lit 44226) k)
        (tStep QA4 QB4 QP4 QD4 (nat_lit 44226) (nat_lit 0) k)))

@[expose] noncomputable def cq4 (c : Nat) : Bool := chunk pr4 (nat_lit 44226) c

@[expose] noncomputable def chStep (P : List (List Nat)) (b k i : Nat) : Bool :=
  Nat.beq (CFSG.KC.Fi24Fix.wordMul CFSG.KD.BrFi24.MUL CFSG.KD.Fi24G2e.LG (CFSG.KC.Fi24Kn.nthW P i)
      (nIf(Nat.blt (Nat.succ i) k, MX (Nat.add b (Nat.succ i)), CFSG.KD.BrFi24.ONE)))
    (MX (Nat.add b i))

@[expose] noncomputable def chA2 (i : Nat) : Bool := chStep J.CA2 (nat_lit 0) (nat_lit 10) i

@[expose] noncomputable def chA4 (i : Nat) : Bool := chStep J.CA4 (nat_lit 10) (nat_lit 11) i

@[expose] noncomputable def chB4 (i : Nat) : Bool := chStep J.CB4 (nat_lit 21) (nat_lit 11) i

@[expose] noncomputable def chS4 (i : Nat) : Bool := chStep J.CS4 (nat_lit 32) (nat_lit 5) i

@[expose] noncomputable def ok0S (c : Nat) : Bool := okS J.S0 J.K0 c

@[expose] noncomputable def ok1 (c : Nat) : Bool := okS J.S1 J.K1 c

@[expose] noncomputable def ok2 (c : Nat) : Bool := okS J.S2 J.K2 c

@[expose] noncomputable def ok3 (c : Nat) : Bool := okS J.S3 J.K3 c

@[expose] noncomputable def ok4 (c : Nat) : Bool := okS J.S4 J.K4 c

end CFSG.KD.Fi24P7

end

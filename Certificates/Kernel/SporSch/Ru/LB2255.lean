module

public import Certificates.Kernel.SporSch.Ru.LB2255Data
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.TreePL
public import Certificates.Data.Kernel.SporSch.Ru2255K
public import Certificates.Kernel.SporSch.Ru.CData
public import Certificates.Kernel.SporSch.Ru.LCData

public section

namespace CertificateChecks.KernelSporSch.RuLB

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2255 CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def jOf (k : Nat) : Nat := ruReps.getD k 0

@[expose] noncomputable def gT (j : Nat) : Nat :=
  pwK 4060 12 (mask 12) A0 A1 (pidn 4060 12) (nat_lit 64) (pathK RuTree.plK (nat_lit 64) j)

@[expose] noncomputable def repOK (k : Nat) : Bool :=
  strictB (gT (jOf k)) (fun G =>
    bAnd(conjK 4060 12 (mask 12) G (TK k) Z, conjRK 4060 12 (mask 12) G A0 (AG k)))

@[expose] noncomputable def oL0 : Nat := roff 4060 (4060 * 12) (RuLS.LR 0)

@[expose] noncomputable def oL1 : Nat := roff 4060 (4060 * 12) (RuLS.LR 1)

@[expose] noncomputable def pCm (k : Nat) (_ _ T0 T1 : Nat) : Bool :=
  cmK 4060 12 (mask 12) T0 T1 (TK k)

@[expose] noncomputable def centOK (k : Nat) : Bool :=
  strictB oL0 (fun o0 => strictB oL1 (fun o1 =>
    Nat.beq (cntK RuLS.TR o0 o1 (nat_lit 64) (pCm k) (nat_lit 0) (nat_lit 1820))
      (ruCentCounts.getD k 0)))

@[expose] def ord14Exp : List Bool :=
  [false, false, false, true, false, false, true, false, false, false, false, true, false,
    false, false, false, false, false, false]

@[expose] noncomputable def atK (k y : Nat) : Nat := pg 12 (mask 12) A0 (pg 12 (mask 12) (TK k) y)

@[expose] noncomputable def ordOK (k : Nat) : Bool :=
  bIf(ord14Exp.getD k false, ordK (atK k), bIf(ordK (atK k), false, true))

@[expose] noncomputable def oC (i : Nat) : Nat := roff 4060 (4060 * 12) (RuCS.LR i)

@[expose] noncomputable def pSq (T0 T1 T2 : Nat) : Bool := sqK 4060 12 (mask 12) T0 T1 T2 Z

@[expose] noncomputable def pFib (k : Nat) (T0 T1 T2 : Nat) : Bool :=
  bAnd(sqK 4060 12 (mask 12) T0 T1 T2 Z, fibK 12 (mask 12) (AG k) T0 T1 T2)

@[expose] noncomputable def fRep (f : Nat) : Nat :=
  nIf(Nat.beq f (nat_lit 1), nat_lit 3, nIf(Nat.beq f (nat_lit 2), nat_lit 6, nat_lit 11))

@[expose] noncomputable def pC (f T0 T1 T2 : Nat) : Bool :=
  bIf(Nat.beq f (nat_lit 0), pSq T0 T1 T2, pFib (fRep f) T0 T1 T2)

@[expose] noncomputable def cntCB (i : Nat) : Nat := pg 16 (mask 16) CNTC i

@[expose] noncomputable def blkC (i : Nat) : Bool :=
  strictB (oC 0) (fun o0 => strictB (oC 1) (fun o1 => strictB (oC 2) (fun o2 =>
    Nat.beq (cnt3K RuCS.TR o0 o1 o2 (nat_lit 64) (nat_lit 2) (pC (Nat.div i (nat_lit 30)))
      (Nat.mul (nat_lit 64) (Nat.mod i (nat_lit 30))) (nat_lit 64)) (cntCB i))))

@[expose] noncomputable def centP (m i : Nat) : Bool := centOK (Nat.add (Nat.mul (nat_lit 5) m) i)

@[expose] noncomputable def blkP (f i : Nat) : Bool := blkC (Nat.add (Nat.mul (nat_lit 30) f) i)

@[expose] noncomputable def totC (f : Nat) : Nat :=
  foldN (nat_lit 30) (fun q s => Nat.add s (cntCB (Nat.add (Nat.mul (nat_lit 30) f) q)))
    (nat_lit 0)

end CertificateChecks.KernelSporSch.RuLB

end

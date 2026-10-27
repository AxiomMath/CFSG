module

public import Certificates.Kernel.SporSch.Ru.LA2254Data
public import Certificates.Kernel.SporSch.Ru.LB2255
public import Certificates.Kernel.SporSch.Ru.WitData
public import Certificates.Data.Kernel.SporSch.Ru2254K

public section

namespace CertificateChecks.KernelSporSch.RuLA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2254 CFSG.Sporadic.RuSchreier
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLB

@[expose] noncomputable def inv (n : Nat) : Nat := pg 16 (mask 16) INV n

@[expose] noncomputable def Y0 (i : Nat) : Nat := RuLS.TR (Nat.add oL0 (ruZLPos.getD i (0, 0)).1)

@[expose] noncomputable def Y1 (i : Nat) : Nat := RuLS.TR (Nat.add oL1 (ruZLPos.getD i (0, 0)).2)

@[expose] noncomputable def commOK : Bool :=
  allN 3 (fun i => strictB (Y0 i) (fun T0 => strictB (Y1 i) (fun T1 =>
    allN 3 (fun j => cmK 4060 12 (mask 12) T0 T1 (RuW.LG j)))))

@[expose] noncomputable def ytK (i k x : Nat) : Nat := tv 12 (mask 12) (Y0 i) (Y1 i) (pg 12 (mask 12) (TK k) x)

@[expose] noncomputable def fixOK (k : Nat) : Bool :=
  allN 3 (fun i => bAnd(Nat.beq (fixCntK 4060 (ytK i k)) (inv (Nat.add (Nat.mul 7 k) (Nat.add 1
    (Nat.mul 2 i)))), Nat.beq (fixCntK 4060 (fun x => ytK i k (ytK i k x)))
      (inv (Nat.add (Nat.mul 7 k) (Nat.add 2 (Nat.mul 2 i))))))

@[expose] noncomputable def pOF (k : Nat) (_ _ T0 T1 : Nat) : Bool :=
  strictB (tv 12 (mask 12) T0 T1 (nat_lit 0)) (fun p => Nat.beq (pg 12 (mask 12) (TK k) p) p)

@[expose] noncomputable def orbOK (k : Nat) : Bool :=
  strictB oL0 (fun o0 => strictB oL1 (fun o1 =>
    Nat.beq (cntK RuLS.TR o0 o1 (nat_lit 64) (pOF k) (nat_lit 0) (nat_lit 1820))
      (inv (Nat.mul 7 k))))

@[expose] noncomputable def orbP (m i : Nat) : Bool := orbOK (Nat.add (Nat.mul (nat_lit 5) m) i)

end CertificateChecks.KernelSporSch.RuLA

end

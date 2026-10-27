module

public import Certificates.Kernel.J4Q.LocM
public import Certificates.Data.Kernel.J4Q.Words26
public import Certificates.Data.J4Ov.WordsE
import Certificates.Kernel.J4Q.Strs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Ov.E4205 CFSG.Quasithin.J4Ov.eData

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Q

theorem eData_strs4205 : CFSG.Quasithin.J4Ov.eData.map Prod.fst =
    [String.ofList E4205.s0, String.ofList E4205.s1, String.ofList E4205.s2,
      String.ofList E4205.s3, String.ofList E4205.s4, String.ofList E4205.s5,
      String.ofList E4205.s6, String.ofList E4205.s7, String.ofList E4205.s8,
      String.ofList E4205.s9, String.ofList E4205.s10, String.ofList E4205.s11] := by
  rw [E4205.eq]
  rfl

@[expose] noncomputable def ew4205 : List (List Int) :=
  [lettersAZ E4205.s0, lettersAZ E4205.s1, lettersAZ E4205.s2, lettersAZ E4205.s3,
    lettersAZ E4205.s4, lettersAZ E4205.s5, lettersAZ E4205.s6, lettersAZ E4205.s7,
    lettersAZ E4205.s8, lettersAZ E4205.s9, lettersAZ E4205.s10, lettersAZ E4205.s11]

@[expose] noncomputable def conj4205 (l : Nat) : List Nat :=
  smapK (fun U => mulJ c rm (mulJ c rm (getN one MLIs (Nat.sub l 1)) U)
    (getN one MLs (Nat.sub l 1))) Us

@[expose] noncomputable def eChk4205 (l i m : Nat) (w : List Int) : Bool :=
  andB (Nat.blt m (nat_lit 2048))
    (Nat.beq (mulJ c rm (wordJ c rm one (List.append Us (conj4205 l))
      (List.append Us (conj4205 l)) w) (getN one [L0i, L1i, L2i] i)) (etaK c rm one Us m))

@[expose] noncomputable def em4205 (t : Nat) : Nat := (CFSG.Quasithin.J4Ov.eData.getD t ("", 0)).2

@[expose] noncomputable def ch4205K (t : Nat) : Bool :=
  eChk4205 (Nat.succ (Nat.div t (nat_lit 3))) (Nat.mod t (nat_lit 3)) (em4205 t) (ew4205.getD t [])

#j4q_all CFSG.KD.J4Ov.ch4205 CertificateChecks.KernelJ4Ov.ch4205K 12

@[expose] noncomputable def mvJ4205 : List Nat := [0, 0, 0, 0]

@[expose] noncomputable def mv4205K (l j : Nat) : Bool :=
  neN (vecJ rm (vecJ rm (vecJ rm (v2N rootV) (getN one MLIs (Nat.sub l 1))) (getN one Us j))
    (getN one MLs (Nat.sub l 1))) (v2N rootV)

theorem mv4205_ok : allR 4 (fun i => andB (Nat.blt (getN 0 mvJ4205 i) 11)
    (mv4205K (Nat.succ i) (getN 0 mvJ4205 i))) = true := by
  quickRfl

theorem ch4205_neg_m : notB (eChk4205 1 0 (em4205 1) (ew4205.getD 0 [])) = true := by
  quickRfl

theorem ch4205_neg_l : notB (eChk4205 1 0 (em4205 3) (ew4205.getD 3 [])) = true := by
  quickRfl

theorem ch4205_neg_i : notB (eChk4205 1 1 (em4205 0) (ew4205.getD 0 [])) = true := by
  quickRfl

end CertificateChecks.KernelJ4Ov

end

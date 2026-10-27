module

public import Certificates.Kernel.J4Q.LocM
public import Certificates.Kernel.J4Q.MaskU
public import Certificates.Data.Kernel.J4Q.Words26
public import Certificates.Data.J4Ov.Reps
public import Certificates.Data.J4Ov.WordsP
import Certificates.Kernel.J4Q.Strs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Ov.R4207 CFSG.Quasithin.J4Ov.repData
#j4q_strs CFSG.KD.J4Ov.P4207 CFSG.Quasithin.J4Ov.pData

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Q
  CFSG.Quasithin.J4Ov

theorem repData_strs4207 : repData.map RepEntry.xw =
    [String.ofList R4207.s43, String.ofList R4207.s44, String.ofList R4207.s45,
      String.ofList R4207.s46, String.ofList R4207.s47, String.ofList R4207.s48,
      String.ofList R4207.s37, String.ofList R4207.s38, String.ofList R4207.s39,
      String.ofList R4207.s40, String.ofList R4207.s41, String.ofList R4207.s42,
      String.ofList R4207.s31, String.ofList R4207.s32, String.ofList R4207.s33,
      String.ofList R4207.s34, String.ofList R4207.s35, String.ofList R4207.s36,
      String.ofList R4207.s25, String.ofList R4207.s26, String.ofList R4207.s27,
      String.ofList R4207.s28, String.ofList R4207.s29, String.ofList R4207.s30,
      String.ofList R4207.s19, String.ofList R4207.s20, String.ofList R4207.s21,
      String.ofList R4207.s22, String.ofList R4207.s23, String.ofList R4207.s24,
      String.ofList R4207.s13, String.ofList R4207.s14, String.ofList R4207.s15,
      String.ofList R4207.s16, String.ofList R4207.s17, String.ofList R4207.s18,
      String.ofList R4207.s7, String.ofList R4207.s8, String.ofList R4207.s9,
      String.ofList R4207.s10, String.ofList R4207.s11, String.ofList R4207.s12,
      String.ofList R4207.s0, String.ofList R4207.s1, String.ofList R4207.s2,
      String.ofList R4207.s3, String.ofList R4207.s4, String.ofList R4207.s5,
      String.ofList R4207.s6] := by
  rw [R4207.eq]
  rfl

theorem pData_strs4207 : pData.map PEntry.w =
    [String.ofList P4207.s39, String.ofList P4207.s40, String.ofList P4207.s41,
      String.ofList P4207.s42, String.ofList P4207.s43, String.ofList P4207.s33,
      String.ofList P4207.s34, String.ofList P4207.s35, String.ofList P4207.s36,
      String.ofList P4207.s37, String.ofList P4207.s38, String.ofList P4207.s28,
      String.ofList P4207.s29, String.ofList P4207.s30, String.ofList P4207.s31,
      String.ofList P4207.s32, String.ofList P4207.s22, String.ofList P4207.s23,
      String.ofList P4207.s24, String.ofList P4207.s25, String.ofList P4207.s26,
      String.ofList P4207.s27, String.ofList P4207.s17, String.ofList P4207.s18,
      String.ofList P4207.s19, String.ofList P4207.s20, String.ofList P4207.s21,
      String.ofList P4207.s11, String.ofList P4207.s12, String.ofList P4207.s13,
      String.ofList P4207.s14, String.ofList P4207.s15, String.ofList P4207.s16,
      String.ofList P4207.s6, String.ofList P4207.s7, String.ofList P4207.s8,
      String.ofList P4207.s9, String.ofList P4207.s10, String.ofList P4207.s0,
      String.ofList P4207.s1, String.ofList P4207.s2, String.ofList P4207.s3,
      String.ofList P4207.s4, String.ofList P4207.s5] := by
  rw [P4207.eq]
  rfl

@[expose] noncomputable def rx4207 : List (List Int) :=
  [R4207.s43, R4207.s44, R4207.s45, R4207.s46, R4207.s47, R4207.s48, R4207.s37, R4207.s38,
    R4207.s39, R4207.s40, R4207.s41, R4207.s42, R4207.s31, R4207.s32, R4207.s33, R4207.s34,
    R4207.s35, R4207.s36, R4207.s25, R4207.s26, R4207.s27, R4207.s28, R4207.s29, R4207.s30,
    R4207.s19, R4207.s20, R4207.s21, R4207.s22, R4207.s23, R4207.s24, R4207.s13, R4207.s14,
    R4207.s15, R4207.s16, R4207.s17, R4207.s18, R4207.s7, R4207.s8, R4207.s9, R4207.s10,
    R4207.s11, R4207.s12, R4207.s0, R4207.s1, R4207.s2, R4207.s3, R4207.s4, R4207.s5,
    R4207.s6].map lettersAZ

@[expose] noncomputable def pw4207 : List (List Int) :=
  [P4207.s39, P4207.s40, P4207.s41, P4207.s42, P4207.s43, P4207.s33, P4207.s34, P4207.s35,
    P4207.s36, P4207.s37, P4207.s38, P4207.s28, P4207.s29, P4207.s30, P4207.s31, P4207.s32,
    P4207.s22, P4207.s23, P4207.s24, P4207.s25, P4207.s26, P4207.s27, P4207.s17, P4207.s18,
    P4207.s19, P4207.s20, P4207.s21, P4207.s11, P4207.s12, P4207.s13, P4207.s14, P4207.s15,
    P4207.s16, P4207.s6, P4207.s7, P4207.s8, P4207.s9, P4207.s10, P4207.s0, P4207.s1,
    P4207.s2, P4207.s3, P4207.s4, P4207.s5].map lettersAZ

@[expose] noncomputable def km4207 : List Nat := [mkKM_0, mkKM_1, mkKM_2, mkKM_3]

@[expose] noncomputable def ki4207 (i : Nat) : Nat :=
  wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] (negRev (mkKW.getD i []))

theorem kinv4207_ok : allR 4 (fun i => andB (canonJ pad (ki4207 i))
    (Nat.beq (mulJ c rm (getN one km4207 i) (ki4207 i)) one)) = true := by
  quickRfl

@[expose] noncomputable def rep4207 (i : Nat) : RepEntry := repData.getD i ⟨0, "", true, 0⟩

@[expose] noncomputable def z4207 (i : Nat) : Nat :=
  mulJ c rm (getN one MLs (Nat.sub (rep4207 i).l 1))
    (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] (rx4207.getD i []))

@[expose] noncomputable def zi4207 (i : Nat) : Nat :=
  mulJ c rm (wordJ c rm one [L0, L1, L2] [L0i, L1i, L2i] (negRev (rx4207.getD i [])))
    (getN one MLIs (Nat.sub (rep4207 i).l 1))

@[expose] noncomputable def pFacts4207 (Z Zi : Nat) (C : List Nat) (W p m : Nat) : Bool :=
  andB (Nat.beq (mulJ c rm Z Zi) one) (andB (canonJ pad Zi)
  (andB (Nat.beq (vecJ rm (v2N rootV) W) (v2N rootV))
  (andB (orB (Nat.beq p 11) (Nat.beq p 23)) (andB (Nat.blt m 2048)
  (strictB (etaK c rm one Us m) fun E =>
    andB (Nat.beq (powJ c rm one W p) E) (andB (neN W E)
      (notB (allR 11 fun j => Nat.beq (vecJ rm (v2N rootV) (getN one C j)) (v2N rootV)))))))))

@[expose] noncomputable def pChk4207 (i : Nat) (w : List Int) (p m : Nat) : Bool :=
  andB (notB (rep4207 i).exc)
    (strictB (z4207 i) fun Z => strictB (zi4207 i) fun Zi =>
      (fun C => strictB (wordJ c rm one (List.append Us (List.append km4207 C))
          (List.append Us (List.append [ki4207 0, ki4207 1, ki4207 2, ki4207 3] C)) w) fun W =>
        pFacts4207 Z Zi C W p m)
      (smapK (fun U => mulJ c rm (mulJ c rm Zi U) Z) Us))

@[expose] noncomputable def pEnt4207 (t : Nat) : PEntry := pData.getD t ⟨0, "", 0, 0⟩

@[expose] noncomputable def ch4207K (t : Nat) : Bool :=
  pChk4207 (pEnt4207 t).idx (pw4207.getD t []) (pEnt4207 t).p (pEnt4207 t).c

#j4q_all CFSG.KD.J4Ov.ch4207 CertificateChecks.KernelJ4Ov.ch4207K 44

theorem cover4207_ok : andB (Nat.beq pData.length 44) (allR 49 fun i =>
    orB (rep4207 i).exc (pData.any fun e => Nat.beq e.idx i)) = true := by
  quickRfl

theorem ch4207_neg_m : notB (pChk4207 0 (pw4207.getD 0 []) 11 333) = true := by
  quickRfl

theorem ch4207_neg_p : notB (pChk4207 2 (pw4207.getD 2 []) 11 0) = true := by
  quickRfl

theorem ch4207_neg_r : notB (pChk4207 0 (pw4207.getD 1 []) 11 333) = true := by
  quickRfl

theorem ch4207_neg_e : notB (pChk4207 18 (pw4207.getD 0 []) 11 0) = true := by
  quickRfl

end CertificateChecks.KernelJ4Ov

end

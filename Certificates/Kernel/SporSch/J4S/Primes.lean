
module

public import Certificates.Kernel.SporSch.J4S.XY
public import CFSG.Certificates.Kernel.SporSch.J4SPrimesSound
public import CFSG.Certificates.Kernel.Spor.Loops
meta import CFSG.Sporadic.Schreier.J4SPrimes
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

set_option maxRecDepth 400000

#kss_array CertificateChecks.KernelSporSch.J4Q5 CFSG.Sporadic.J4Schreier.q5Cols 11 11
#kss_array CertificateChecks.KernelSporSch.J4Q7 CFSG.Sporadic.J4Schreier.q7Cols 11 11
#kss_array CertificateChecks.KernelSporSch.J4Q23 CFSG.Sporadic.J4Schreier.q23Cols 11 11
#kss_array CertificateChecks.KernelSporSch.J4B CFSG.Sporadic.J4Schreier.B23 11 11
#kss_array CertificateChecks.KernelSporSch.J4BI CFSG.Sporadic.J4Schreier.B23inv 11 11

namespace CertificateChecks.KernelSporSch.J4Primes

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

@[expose] def QPL : List Nat := [1329552593586084350528447794605199361,
  1122107770997488547144362077963688701, 2574121737587235088920960795934722056,
  2019440854590709524279784930576690046, 861641762460103307005411688244592876,
  2643687189619968787163121056657176188, 1931727748449939449011879564494201652,
  1398680273872105191366312427764572626, 1642082899011134635818911065358049494,
  2390943328309830785456040448585798479, 1636942012460782680860655359673938911]

@[expose] noncomputable def QP (i : Nat) : Nat := nget QPL i

@[expose] noncomputable def PC (w : Nat) : Nat := packK fun i => appK (QP i) w

@[expose] noncomputable def neId (P : Nat) : Bool :=
  bAnd(canonK P, bAnd(canonK pidK, Bool.not (Nat.beq P pidK)))

theorem qp : allN 11 (fun i => Nat.beq (powKF 32 J4Q23 i) (QP i)) = true := by quickRfl

theorem p5 : Nat.beq (powKF 32 (W bWord) 48964608) J4Q5 = true := by quickRfl
theorem o5 : Nat.beq (powKF 32 J4Q5 5) pidK = true := by quickRfl
theorem n5 : neId J4Q5 = true := by quickRfl
theorem f5 : Nat.beq (fixCntK J4Q5) 8 = true := by quickRfl

theorem p7 : Nat.beq (powKF 32 (W w7) 2) J4Q7 = true := by quickRfl
theorem o7 : Nat.beq (powKF 32 J4Q7 7) pidK = true := by quickRfl
theorem n7 : neId J4Q7 = true := by quickRfl
theorem f7 : Nat.beq (fixCntK J4Q7) 4 = true := by quickRfl

theorem p23 : Nat.beq (powKF 32 (W w23) 10644480) J4Q23 = true := by quickRfl
theorem o23 : Nat.beq (powKF 32 J4Q23 23) pidK = true := by quickRfl
theorem n23 : neId J4Q23 = true := by quickRfl

theorem pb : Nat.beq (PC 1) J4B = true := by quickRfl
theorem bb : Nat.beq (compK J4B J4BI) pidK = true := by quickRfl

@[expose] noncomputable def uK (w : Nat) : Bool :=
  bIf(Nat.beq w 1, true, neId (powKF 32 (compK (PC w) J4BI) 11))

end CertificateChecks.KernelSporSch.J4Primes

#kss_slices CertificateChecks.KernelSporSch.J4Primes.U CertificateChecks.KernelSporSch.J4Primes.uK
  64 32

namespace CertificateChecks.KernelSporSch.J4Primes

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4XY

theorem uniq (w : Nat) (hw : w < 2048) : uK w = true := by
  have h := allBlk_spec (U.all (w / 64) (by change w / 64 < 32; omega)) (w % 64) (Nat.mod_lt _ (by omega))
  rwa [show Nat.add (Nat.mul 64 (w / 64)) (w % 64) = w from Nat.div_add_mod w 64] at h

theorem pw (P m : Nat) (hm : m < 2 ^ 32) : powCols (unpack11 P) m = unpack11 (powKF 32 P m) :=
  powKF_eq 32 P m hm

theorem hQP : ∀ i < 11, powCols q23Cols i = unpack11 (QP i) := by
  intro i hi
  rw [show q23Cols = unpack11 J4Q23 from bindW_sound J4Q23.bind]
  exact (pw _ _ (by omega)).trans (congrArg unpack11 (Nat.eq_of_beq_eq_true (allN_spec qp i hi)))

theorem pc_eq (w : Nat) : polyCols w = unpack11 (PC w) := poly_sound hQP (Nat.beq_refl _)

theorem bnd (P : Nat) : Bounded (unpack11 P) := unpack11_bounded P

theorem ne1 {P : Nat} (h : neId P = true) : unpack11 P ≠ idRows 11 := by
  rw [CFSG.KS.SporSch.C11.id_eq]
  exact ne_sound h

theorem facts : (powCols (wordCols bWord) 48964608 = q5Cols)
    ∧ (powCols q5Cols 5 = idRows 11 ∧ q5Cols ≠ idRows 11 ∧ fixCount q5Cols = 8 ∧
      Bounded q5Cols)
    ∧ (powCols (wordCols w7) 2 = q7Cols)
    ∧ (powCols q7Cols 7 = idRows 11 ∧ q7Cols ≠ idRows 11 ∧ fixCount q7Cols = 4 ∧
      Bounded q7Cols)
    ∧ (powCols (wordCols w23) 10644480 = q23Cols)
    ∧ (powCols q23Cols 23 = idRows 11 ∧ q23Cols ≠ idRows 11 ∧ Bounded q23Cols)
    ∧ (B23 = polyCols 1 ∧ comp11 B23 B23inv = idRows 11 ∧ Bounded B23 ∧
      Bounded B23inv)
    ∧ (∀ w < 2048, Bounded (polyCols w))
    ∧ (∀ w < 2048, powCols (comp11 (polyCols w) B23inv) 11 = idRows 11 → w = 1)
    ∧ (Bounded (idRows 11)) := by
  have q5 : q5Cols = unpack11 J4Q5 := bindW_sound J4Q5.bind
  have q7 : q7Cols = unpack11 J4Q7 := bindW_sound J4Q7.bind
  have q23 : q23Cols = unpack11 J4Q23 := bindW_sound J4Q23.bind
  have b : B23 = unpack11 J4B := bindW_sound J4B.bind
  have bi : B23inv = unpack11 J4BI := bindW_sound J4BI.bind
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    fun w _ => ?_, fun w hw h => ?_, ?_⟩
  · rw [wordCols_eq', pw _ _ (by norm_num), q5]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true p5)
  · rw [q5, pw _ _ (by norm_num), CFSG.KS.SporSch.C11.id_eq]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true o5)
  · rw [q5]
    exact ne1 n5
  · rw [q5]
    exact fix_sound f5
  · rw [q5]
    exact bnd _
  · rw [wordCols_eq', pw _ _ (by norm_num), q7]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true p7)
  · rw [q7, pw _ _ (by norm_num), CFSG.KS.SporSch.C11.id_eq]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true o7)
  · rw [q7]
    exact ne1 n7
  · rw [q7]
    exact fix_sound f7
  · rw [q7]
    exact bnd _
  · rw [wordCols_eq', pw _ _ (by norm_num), q23]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true p23)
  · rw [q23, pw _ _ (by norm_num), CFSG.KS.SporSch.C11.id_eq]
    exact congrArg unpack11 (Nat.eq_of_beq_eq_true o23)
  · rw [q23]
    exact ne1 n23
  · rw [q23]
    exact bnd _
  · rw [pc_eq, b]
    exact (congrArg unpack11 (Nat.eq_of_beq_eq_true pb)).symm
  · rw [b, bi, CFSG.KS.SporSch.C11.id_eq]
    exact comp_sound bb
  · rw [b]
    exact bnd _
  · rw [bi]
    exact bnd _
  · rw [pc_eq]
    exact bnd _
  · by_contra hne
    have hk := uniq w hw
    unfold uK at hk
    rw [show Nat.beq w 1 = false from Bool.eq_false_iff.2 fun e => hne (Nat.eq_of_beq_eq_true e)]
      at hk
    rw [pc_eq, bi, comp_eq, pw _ _ (by norm_num)] at h
    exact ne1 hk h
  · rw [CFSG.KS.SporSch.C11.id_eq]
    exact bnd _

end CertificateChecks.KernelSporSch.J4Primes

end

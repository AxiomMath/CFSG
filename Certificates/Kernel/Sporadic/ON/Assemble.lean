module

public import Certificates.Kernel.Sporadic.ON.Data
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.ONSeedA CFSG.Sporadic.ON.Native.seedA

#ks_chars CertificateChecks.KernelSpor.ONSeedB CFSG.Sporadic.ON.Native.seedB

#ks_chars CertificateChecks.KernelSpor.ONRoot CFSG.ONSchreier.Data.rootDigits

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native

variable (mvAll : ∀ s < 1023, mvS s = true) (ordAll : ∀ s < 1023, ordS s = true)
  (sortAll : ∀ s < 1023, sortS s = true) (trAll : ∀ s < 1023, trS s = true)

theorem colsAK : colsK ONV.CA ONSeedA.chars = true := by quickRfl
theorem colsBK : colsK ONV.CB ONSeedB.chars = true := by quickRfl
theorem rootK : digitsK ONRoot.chars (key ONV.K 0) = true := by quickRfl
theorem listA : allN 154 (fun j => Nat.beq (List.getD ONV.LA j 0) (ONV.CA j)) = true := by quickRfl
theorem listB : allN 154 (fun j => Nat.beq (List.getD ONV.LB j 0) (ONV.CB j)) = true := by quickRfl
theorem nx0 : Nat.beq (ONV.NX 0) 1 = true := by quickRfl
theorem nx1 : Nat.beq (ONV.NX 1023) 245520 = true := by quickRfl

theorem pt_of {F : Nat → Bool} {G : Nat → Bool} (hF : ∀ s < 1023, F s = true)
    (hG : ∀ s, F s = allBlk (Nat.mul s (nat_lit 240)) G (nat_lit 240)) :
    ∀ h < 245520, G h = true := by
  intro h hh
  have := allBlk_spec (hG (h / 240) ▸ hF (h / 240) (by omega)) (h % 240) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (h / 240) 240) (h % 240) = h := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  rwa [e] at this

theorem list_eq (L : List Nat) (C : Nat → Nat) (h : ∀ j < 154, Nat.beq (L.getD j 0) (C j) = true) :
    ∀ j < 154, L.getD j 0 = C j := fun j hj => Nat.eq_of_beq_eq_true (h j hj)

theorem cols_of {C : Nat → Nat} {L : List Nat} {cs : List Char} {s : String} (hs : s = String.ofList cs)
    (hk : colsK C cs = true) (hl : ∀ j < 154, L.getD j 0 = C j) (hlen : L.length = 154) :
    ((transpose 154 (rowsOf 154 s)).map ofV).size = 154 ∧ L.length = 154 ∧
      ∀ j < 154, ((transpose 154 (rowsOf 154 s)).map ofV)[j]! = wOfK (L.getD j 0) := by
  subst hs
  refine ⟨by simp [transpose], hlen, fun j hj => ?_⟩
  rw [hl j hj]
  exact colsK_sound hk j hj

theorem canon_of {C : Nat → Nat} {L : List Nat} {cs : List Char} (hk : colsK C cs = true)
    (hl : ∀ j < 154, L.getD j 0 = C j) : ∀ j < 154, canon (L.getD j 0) = true := by
  intro j hj
  rw [hl j hj]
  exact allN_spec ((bAnd_iff _ _).1 hk).1 j hj

include mvAll ordAll sortAll in
theorem orb_tabs : natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha = tabArr ONV.A 245520 ∧
    natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta = tabArr ONV.B 245520 := by
  have hla := list_eq ONV.LA ONV.CA (allN_spec listA)
  have hlb := list_eq ONV.LB ONV.CB (allN_spec listB)
  have hA : colsA.size = 154 ∧ ONV.LA.length = 154 ∧ ∀ j < 154, colsA[j]! = wOfK (ONV.LA.getD j 0) := by
    unfold colsA rowsA
    exact cols_of ONSeedA.eq colsAK hla rfl
  have hB : colsB.size = 154 ∧ ONV.LB.length = 154 ∧ ∀ j < 154, colsB[j]! = wOfK (ONV.LB.getD j 0) := by
    unfold colsB rowsB
    exact cols_of ONSeedB.eq colsBK hlb rfl
  unfold vorbit
  rw [ONRoot.eq, digitsK_sound rootK]
  exact bfsK_sound (SL := 240) (NS := 1023) (SO := ONV.SO) (SOI := ONV.SOI) (NX := ONV.NX) (K := ONV.K)
    hA hB (canon_of colsAK hla) (canon_of colsBK hlb) rfl (by norm_num)
    (pt_of mvAll fun _ => rfl) (by norm_num) (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1)
    ordAll (pt_of sortAll fun _ => rfl)

theorem words_ok : CFSG.ONSchreier.Data.strongWords.size = 7 ∧
    (CFSG.ONSchreier.Data.strongWords[0]! = [] ∧ CFSG.ONSchreier.Data.strongWords[1]! = []) ∧
    ∀ j < 7, 2 ≤ j → encW CFSG.ONSchreier.Data.strongWords[j]! = ONV.WC j ∧
      (CFSG.ONSchreier.Data.strongWords[j]!).length = ONV.WL j ∧
      plettersOK j CFSG.ONSchreier.Data.strongWords[j]! = true := by
  decide

include mvAll ordAll sortAll trAll in
theorem qon_eq : CFSG.ONSchreier.qonStrongArrs =
    Array.ofFn (n := 7) fun j => Array.ofFn (n := 245520) fun i => TT j.val i.val := by
  obtain ⟨ha, hb⟩ := orb_tabs mvAll ordAll sortAll
  obtain ⟨w1, w2, w3⟩ := words_ok
  unfold CFSG.ONSchreier.qonStrongArrs
  rw [ha, hb]
  exact strongK_sound (TT := TT) (UU := UU) w1 (by norm_num) (by norm_num) w2 w3 (pt_of trAll fun _ => rfl)

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

include trAll in
theorem perm_facts : ∀ x < 245520, ∀ j < 7, TT j x < 245520 ∧ UU j x < 245520 ∧ UU j (TT j x) = x := by
  intro x hx j hj
  have h := pt_of trAll (fun _ => rfl) x hx
  have h2 := allBlk_spec ((bAnd_iff _ _).1 h).1 j hj
  rw [Nat.add_eq, Nat.zero_add] at h2
  rw [strictB_eq'] at h2
  obtain ⟨a1, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨a2, a3⟩ := (bAnd_iff _ _).1 h4
  exact ⟨Nat.blt_eq ▸ a1, Nat.blt_eq ▸ a2, Nat.eq_of_beq_eq_true a3⟩

end CertificateChecks.KernelSpor.ON

end

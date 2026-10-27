
module

public import Certificates.Kernel.Sporadic.ON.Levels
public import Certificates.Kernel.Sporadic.ON.Neg
public import CFSG.Certificates.Kernel.Spor.ONNegSound
public import CFSG.Certificates.Kernel.Spor.CBTrInv
public import CFSG.Sporadic.ONOddCore.MinusCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.ON.Setup
public import CFSG.Sporadic.ON.VecSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native CFSG.Sporadic.ONOddCore

theorem ofFn_get {α : Type} [Inhabited α] {n k : Nat} {f : Fin n → α} (h : k < n) :
    (Array.ofFn (n := n) f)[k]! = f ⟨k, h⟩ := by
  rw [getElem!_pos _ k (by simpa using h), Array.getElem_ofFn]

theorem keys_eq : (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).keys =
    Array.ofFn (n := 245520) fun i => wOfK (key ONV.K i.val) := by
  have hla := list_eq ONV.LA ONV.CA (allN_spec listA)
  have hlb := list_eq ONV.LB ONV.CB (allN_spec listB)
  have hA : (CFSG.Sporadic.ON.Native.colsA ()).size = 154 ∧ ONV.LA.length = 154 ∧
      ∀ j < 154, (CFSG.Sporadic.ON.Native.colsA ())[j]! = wOfK (ONV.LA.getD j 0) := by
    unfold CFSG.Sporadic.ON.Native.colsA rowsA
    exact cols_of ONSeedA.eq colsAK hla rfl
  have hB : (CFSG.Sporadic.ON.Native.colsB ()).size = 154 ∧ ONV.LB.length = 154 ∧
      ∀ j < 154, (CFSG.Sporadic.ON.Native.colsB ())[j]! = wOfK (ONV.LB.getD j 0) := by
    unfold CFSG.Sporadic.ON.Native.colsB rowsB
    exact cols_of ONSeedB.eq colsBK hlb rfl
  unfold vorbit
  rw [ONRoot.eq, digitsK_sound rootK]
  exact bfsK_keys (SL := 240) (NS := 1023) (SO := ONV.SO) (SOI := ONV.SOI) (NX := ONV.NX)
    (K := ONV.K) hA hB (canon_of colsAK hla) (canon_of colsBK hlb) rfl (by norm_num)
    (pt_of mvAll fun _ => rfl) (by norm_num) (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1)
    ordAll (pt_of sortAll fun _ => rfl)

theorem canon_key : ∀ h < 245520, canon (key ONV.K h) = true := by
  intro h hh
  have e := pt_of mvAll (fun _ => rfl) h hh
  unfold mvAt at e
  simp only [strictB_eq'] at e
  exact ((bAnd_iff _ _).1 e).1

theorem sigma_eq : sigmaArr = Array.ofFn (n := 245520) fun i => tab ONN.NEG i.val := by
  unfold sigmaArr
  have hk := keys_eq
  exact sigma_sound hk canon_key (pt_of sortAll fun _ => rfl) (pt_of negAll fun _ => rfl)

theorem neg_facts {i : Nat} (hi : i < 245520) :
    tab ONN.NEG i < 245520 ∧ tab ONN.NEG (tab ONN.NEG i) = i := by
  have e := pt_of negAll (fun _ => rfl) i hi
  unfold negAt at e
  rw [strictB_eq'] at e
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 e
  obtain ⟨-, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨Nat.blt_eq ▸ h1, Nat.eq_of_beq_eq_true h3⟩

theorem sig_inv : pisInv nPts sigmaArr sigmaArr = true := by
  rw [sigma_eq]
  unfold pisInv allBelowN
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  rintro ⟨i, hi⟩ -
  obtain ⟨h1, h2⟩ := neg_facts hi
  simp only [ofFn_get hi, ofFn_get h1, h2, h1, decide_true, Bool.true_and, beq_self_eq_true]

theorem parlab {i : Nat} (hi : i < 2) :
    ∀ k < Mf i, PARf i k < Mf i ∧ LABf i k < Nat.mul 2 (len i) := by
  intro k hk
  have hp : cbPt 245520 (Mf i) (Nat.mul 2 (len i)) (stepF i) (PTSf i) (POSf i) (PARf i) (LABf i) k = true := by
    interval_cases i
    · exact ptL_of pt0All (by decide) k hk
    · exact ptL_of pt1All (by decide) k hk
  unfold cbPt at hp
  rw [strictB_eq', strictB_eq', strictB_eq'] at hp
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 hp
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h, -⟩ := (bAnd_iff _ _).1 h
  by_cases h0 : k = 0
  · subst h0
    interval_cases i <;> decide
  · have hb : Nat.beq k (nat_lit 0) = false := by
      cases k with
      | zero => exact absurd rfl h0
      | succ k => rfl
    rw [hb] at h
    obtain ⟨a, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨b, -⟩ := (bAnd_iff _ _).1 h
    exact ⟨by have := Nat.blt_eq ▸ a; omega, Nat.blt_eq ▸ b⟩

theorem beq_ne {h k : Nat} (hk : h ≠ k) : Nat.beq h k = false := by
  cases e : Nat.beq h k
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) hk

theorem TT_lt {h x : Nat} (hx : x < 245520) : TT h x < 245520 := by
  rcases Nat.lt_or_ge h 7 with h7 | h7
  · exact (perm_facts' x hx h h7).1
  · have e : TT h x = TT 6 x := by
      unfold TT
      rw [beq_ne (by omega : h ≠ 0), beq_ne (by omega : h ≠ 1), beq_ne (by omega : h ≠ 2),
        beq_ne (by omega : h ≠ 3), beq_ne (by omega : h ≠ 4), beq_ne (by omega : h ≠ 5)]
      rfl
    rw [e]
    exact (perm_facts' x hx 6 (by norm_num)).1

theorem UU_lt {h x : Nat} (hx : x < 245520) : UU h x < 245520 := by
  rcases Nat.lt_or_ge h 7 with h7 | h7
  · exact (perm_facts' x hx h h7).2.1
  · have e : UU h x = UU 6 x := by
      unfold UU
      rw [beq_ne (by omega : h ≠ 0), beq_ne (by omega : h ≠ 1), beq_ne (by omega : h ≠ 2),
        beq_ne (by omega : h ≠ 3), beq_ne (by omega : h ≠ 4), beq_ne (by omega : h ≠ 5)]
      rfl
    rw [e]
    exact (perm_facts' x hx 6 (by norm_num)).2.1

theorem invs_of {i : Nat} (hi : i < 2) : ∀ j < Nat.mul 2 (len i), ∀ x < 245520,
    (((allInvSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
      CFSG.ONSchreier.Data.baseList.toArray)[i]!)[j]!)[x]! = invF i j x ∧ invF i j x < 245520 := by
  intro j hj x hx
  refine ⟨invSteps_get' (by omega) hj hx, ?_⟩
  unfold invF
  cases Nat.blt j (len i)
  · exact TT_lt hx
  · exact UU_lt hx

theorem num : bAnd(Nat.beq (tab ONN.NEG (bK 0)) 24, bAnd(Nat.beq (tab ONN.NEG (bK 1)) 72061,
    bAnd(Nat.beq (tab ONN.NEG (bK 2)) 214183, bAnd(Nat.beq (POSf 0 24) 183,
    bAnd(Nat.beq (trInvK (PARf 0) (LABf 0) (invF 0) 245520 183 72061) 73447,
    bAnd(Nat.beq (POSf 1 73447) 22777,
    bAnd(Nat.beq (trInvK (PARf 0) (LABf 0) (invF 0) 245520 183 214183) 241822,
    bAnd(Nat.beq (trInvK (PARf 1) (LABf 1) (invF 1) 52136 22777 241822) 81515,
    bAnd(Nat.beq (POSf 2 81515) 245520, bAnd(Nat.beq (Mf 0) 245520, bAnd(Nat.beq (Mf 1) 52136,
    bAnd(Nat.beq (Mf 2) 36, Nat.beq (bK 2) 100817)))))))))))) = true := by quickRfl

theorem facts : minusOK CFSG.ONSchreier.qonStrongArrs CFSG.ONSchreier.Data.baseList.toArray sigmaArr =
    true := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13⟩ := (by simpa only [bAnd_iff] using num :
    Nat.beq (tab ONN.NEG (bK 0)) 24 = true ∧ Nat.beq (tab ONN.NEG (bK 1)) 72061 = true ∧
    Nat.beq (tab ONN.NEG (bK 2)) 214183 = true ∧ Nat.beq (POSf 0 24) 183 = true ∧
    Nat.beq (trInvK (PARf 0) (LABf 0) (invF 0) 245520 183 72061) 73447 = true ∧
    Nat.beq (POSf 1 73447) 22777 = true ∧
    Nat.beq (trInvK (PARf 0) (LABf 0) (invF 0) 245520 183 214183) 241822 = true ∧
    Nat.beq (trInvK (PARf 1) (LABf 1) (invF 1) 52136 22777 241822) 81515 = true ∧
    Nat.beq (POSf 2 81515) 245520 = true ∧ Nat.beq (Mf 0) 245520 = true ∧
    Nat.beq (Mf 1) 52136 = true ∧ Nat.beq (Mf 2) 36 = true ∧ Nat.beq (bK 2) 100817 = true)
  have m0 : Mf 0 = 245520 := Nat.eq_of_beq_eq_true n10
  have m1 : Mf 1 = 52136 := Nat.eq_of_beq_eq_true n11
  have m2 : Mf 2 = 36 := Nat.eq_of_beq_eq_true n12
  have hL := cLevels_eq'
  have hs0 : sigmaArr[CFSG.ONSchreier.Data.baseList.toArray[0]!]! = 24 := by
    rw [base_get (by norm_num), sigma_eq, ofFn_get (bK_lt (by norm_num))]
    exact Nat.eq_of_beq_eq_true n1
  have hs1 : sigmaArr[CFSG.ONSchreier.Data.baseList.toArray[1]!]! = 72061 := by
    rw [base_get (by norm_num), sigma_eq, ofFn_get (bK_lt (by norm_num))]
    exact Nat.eq_of_beq_eq_true n2
  have hb2 : CFSG.ONSchreier.Data.baseList.toArray[2]! = 100817 := by
    rw [base_get (by norm_num)]
    exact Nat.eq_of_beq_eq_true n13
  have hs2 : sigmaArr[(100817 : Nat)]! = 214183 := by
    rw [← hb2, base_get (by norm_num), sigma_eq, ofFn_get (bK_lt (by norm_num))]
    exact Nat.eq_of_beq_eq_true n3
  have tr0 : ∀ k p, k < Mf 0 → p < 245520 →
      trInvApp (allInvSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
        CFSG.ONSchreier.Data.baseList.toArray)[0]!
        ⟨Array.ofFn (n := Mf 0) fun k => PTSf 0 k.val, Array.ofFn (n := 245520) fun z => POSf 0 z.val,
          Array.ofFn (n := Mf 0) fun k => PARf 0 k.val, Array.ofFn (n := Mf 0) fun k => LABf 0 k.val⟩
        (Mf 0) k p = trInvK (PARf 0) (LABf 0) (invF 0) (Mf 0) k p :=
    fun k p hk hp => trInvApp_eq (parlab (by norm_num)) (invs_of (by norm_num)) (Mf 0) k p hk hp
  have tr1 : ∀ k p, k < Mf 1 → p < 245520 →
      trInvApp (allInvSteps CFSG.ONSchreier.qonStrongArrs (pinvs 245520 CFSG.ONSchreier.qonStrongArrs)
        CFSG.ONSchreier.Data.baseList.toArray)[1]!
        ⟨Array.ofFn (n := Mf 1) fun k => PTSf 1 k.val, Array.ofFn (n := 245520) fun z => POSf 1 z.val,
          Array.ofFn (n := Mf 1) fun k => PARf 1 k.val, Array.ofFn (n := Mf 1) fun k => LABf 1 k.val⟩
        (Mf 1) k p = trInvK (PARf 1) (LABf 1) (invF 1) (Mf 1) k p :=
    fun k p hk hp => trInvApp_eq (parlab (by norm_num)) (invs_of (by norm_num)) (Mf 1) k p hk hp
  unfold minusOK
  simp only [hL, ofFn_get (by norm_num : 0 < 29), ofFn_get (by norm_num : 1 < 29),
    ofFn_get (by norm_num : 2 < 29), Array.size_ofFn, hs0, hs1, hs2, hb2, sig_inv]
  rw [ofFn_get (by norm_num : 24 < 245520), Nat.eq_of_beq_eq_true n4]
  rw [tr0 183 72061 (by rw [m0]; norm_num) (by norm_num),
    tr0 183 214183 (by rw [m0]; norm_num) (by norm_num), m0, Nat.eq_of_beq_eq_true n5,
    Nat.eq_of_beq_eq_true n7]
  rw [ofFn_get (by norm_num : 73447 < 245520), Nat.eq_of_beq_eq_true n6]
  rw [tr1 22777 241822 (by rw [m1]; norm_num) (by norm_num), m1, Nat.eq_of_beq_eq_true n8]
  rw [ofFn_get (by norm_num : 81515 < 245520), Nat.eq_of_beq_eq_true n9, m2]
  decide

end CertificateChecks.KernelSpor.ON

end

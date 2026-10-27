module

public import Certificates.Kernel.HN1408.AKCntFacts
public import Certificates.Certificate441663Base

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.AK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.EvenSporadicStandard.HNRecog.HaradaLA
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KD.HN1408

theorem bt_eq (k i : Nat) : bt k i = bitOf k i := Nat.and_one_is_mod _

theorem bitOf_lt (k i : Nat) : bitOf k i < 2 := Nat.mod_lt _ (by norm_num)

theorem sel_eq (k i : Nat) (g : Equiv.Perm (Fin 1408)) : sel (bs k i) g = g ^ bitOf k i := by
  have e : bs k i = Nat.beq (bitOf k i) 1 := by
    unfold bs
    rw [bt_eq]
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (k >>> i) with h | h
  · have h' : bitOf k i = 0 := h
    rw [h', pow_zero]
    rfl
  · have h' : bitOf k i = 1 := h
    rw [h', pow_one]
    rfl

theorem vc_val (k : Nat) (i : Fin 6) : (vecOfCode k i).val = bitOf k i.val := by
  simp only [vecOfCode, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (bitOf_lt k i.val)

theorem itE_eq (k : Nat) : itE k = uE 0 ^ bitOf k 0 * (uE 1 ^ bitOf k 1 * (uE 2 ^ bitOf k 2 *
    (uE 3 ^ bitOf k 3 * (uE 4 ^ bitOf k 4 * uE 5 ^ bitOf k 5)))) := by
  unfold itE
  rw [sel_eq, sel_eq, sel_eq, sel_eq, sel_eq, sel_eq]

theorem coe_iota (k : Nat) :
    ((iotaFun (vecOfCode k) : ↥P1408) : Equiv.Perm (Fin 1408)) = itE k := by
  unfold iotaFun
  simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  rw [vc_val k 0, vc_val k 1, vc_val k 2, vc_val k 3, vc_val k 4, vc_val k 5, itE_eq]
  simp only [mul_assoc]
  rfl

theorem coe_uElem (i : Nat) : ((uElem i : ↥P1408) : Equiv.Perm (Fin 1408)) = uE i := rfl

theorem itE_45 : itE 45 = elemZ₁ := by
  rw [itE_eq, ← z1_eq]
  have h : bitOf 45 0 = 1 ∧ bitOf 45 1 = 0 ∧ bitOf 45 2 = 1 ∧ bitOf 45 3 = 1 ∧ bitOf 45 4 = 0 ∧
      bitOf 45 5 = 1 := by decide
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  rw [h0, h1, h2, h3, h4, h5]
  simp only [pow_zero, pow_one, one_mul]

theorem itE_32 : itE 32 = elemB := by
  rw [itE_eq]
  have h : bitOf 32 0 = 0 ∧ bitOf 32 1 = 0 ∧ bitOf 32 2 = 0 ∧ bitOf 32 3 = 0 ∧ bitOf 32 4 = 0 ∧
      bitOf 32 5 = 1 := by decide
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  rw [h0, h1, h2, h3, h4, h5]
  simp only [pow_zero, pow_one, one_mul]
  have e : uWords.getD 5 [] = wordB := by decide
  rw [uE, e]
  rfl

theorem pow_blocks {i : Nat} (hi : i < 5) (b : Nat) : uE i ^ b ∈ blocks1408 :=
  pow_mem (u_blocks hi) b

theorem itE_blocks_iff (k : Nat) : itE k ∈ blocks1408 ↔ lamC k = 0 := by
  have hX : uE 0 ^ bitOf k 0 * (uE 1 ^ bitOf k 1 * (uE 2 ^ bitOf k 2 * (uE 3 ^ bitOf k 3 *
      uE 4 ^ bitOf k 4))) ∈ blocks1408 :=
    mul_mem (pow_blocks (by norm_num) _) (mul_mem (pow_blocks (by norm_num) _)
      (mul_mem (pow_blocks (by norm_num) _) (mul_mem (pow_blocks (by norm_num) _)
        (pow_blocks (by norm_num) _))))
  have e : itE k = (uE 0 ^ bitOf k 0 * (uE 1 ^ bitOf k 1 * (uE 2 ^ bitOf k 2 *
      (uE 3 ^ bitOf k 3 * uE 4 ^ bitOf k 4)))) * uE 5 ^ bitOf k 5 := by
    rw [itE_eq]
    simp only [mul_assoc]
  rw [e]
  have hl : lamC k = bitOf k 5 := rfl
  rcases Nat.mod_two_eq_zero_or_one (k >>> 5) with h | h
  · have h' : bitOf k 5 = 0 := h
    rw [hl, h', pow_zero, mul_one]
    exact ⟨fun _ => rfl, fun _ => hX⟩
  · have h' : bitOf k 5 = 1 := h
    rw [hl, h', pow_one]
    refine ⟨fun hm => absurd ?_ u5_not_blocks, fun h1 => absurd h1 (by norm_num)⟩
    have := mul_mem (inv_mem hX) hm
    rwa [inv_mul_cancel_left] at this

theorem conj_blocks {g x : Equiv.Perm (Fin 1408)} (hg : g ∈ blocks1408 ∨ SylTF.Swap g)
    (hx : x ∈ blocks1408) : g * x * g⁻¹ ∈ blocks1408 := by
  rcases hg with hg | hg
  · exact mul_mem (mul_mem hg hx) (inv_mem hg)
  · intro i
    have h1 := hg (x (g⁻¹ i))
    have h2 := hx (g⁻¹ i)
    have h3 := hg (g⁻¹ i)
    have e : g (g⁻¹ i) = i := by simp
    rw [e] at h3
    simp only [Equiv.Perm.mul_apply]
    tauto

theorem normGens_mem {w : List Nat} (hw : w ∈ normGens) : ∃ l < 3, normGens.getD l [] = w := by
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hw
  have hlen : normGens.length = 3 := by decide
  exact ⟨l, by rw [← hlen]; exact hl, List.getD_eq_getElem _ _ hl⟩

theorem aCode_lt : ∀ j < 18, aCode.getD j 0 < 64 := by decide

theorem fuse_pair {kv kw : Nat} (hkv : kv < 64) (hkw : kw < 64) (hv0 : kv ≠ 0) (hv16 : kv ≠ 16)
    (hw0 : kw ≠ 0) (hw16 : kw ≠ 16) (ht : typeIdx kv = typeIdx kw) :
    ∃ n ∈ wordSubgroup normGens, n * itE kv * n⁻¹ = itE kw := by
  obtain ⟨nv, hnv, ev⟩ := fuse_conj _ kv rfl hkv hv0 hv16
  obtain ⟨nw, hnw, ew⟩ := fuse_conj _ kw rfl hkw hw0 hw16
  rw [ht] at ev
  refine ⟨nw * nv⁻¹, mul_mem hnw (inv_mem hnv), ?_⟩
  rw [← ev, ← ew]
  group

theorem lamC_lt (k : Nat) : lamC k < 2 := bitOf_lt k 5

theorem qmC_lt (k : Nat) : qmC k < 2 := Nat.mod_lt _ (by norm_num)

theorem conj_type (hP : Nat.card ↥P1408 = 177408000) {k : Nat} (hk : k < 64) {g : Equiv.Perm (Fin 1408)}
    (hg : g ∈ P1408) (e : g * itE k * g⁻¹ = elemZ₁) : typeIdx k = 2 := by
  have hl : lamC k = 1 := by
    by_contra hne
    have h0 : lamC k = 0 := by have := lamC_lt k; omega
    have hb := conj_blocks (blk_or_swap_P g hg) ((itE_blocks_iff k).2 h0)
    rw [e, ← itE_45, itE_blocks_iff] at hb
    exact absurd hb (by decide)
  have hq : qmC k = 0 := by
    by_contra hne
    have h1 : qmC k = 1 := by have := qmC_lt k; omega
    have ht : typeIdx k = 3 := by
      change 2 * lamC k + qmC k = 3
      rw [hl, h1]
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact absurd hl (by decide)
    have hk16 : k ≠ 16 := by
      rintro rfl
      exact absurd hl (by decide)
    obtain ⟨n, hn, en⟩ := fuse_conj _ k rfl hk hk0 hk16
    rw [ht, show typeBase.getD 3 0 = 32 from rfl, itE_32] at en
    have hnP : n ∈ P1408 := wordSubgroup_le normGens hn
    refine b_not_conj_z₁ hP ⟨(g * n)⁻¹, inv_mem (mul_mem hg hnP), ?_⟩
    rw [← e, ← en]
    group
  change 2 * lamC k + qmC k = 2
  rw [hl, hq]

theorem aFactsK : Certificates.AFacts where
  u_sq i hi := Subtype.ext (u_sq hi)
  u_comm i hi j hj := Subtype.ext (u_comm hi hj)
  iota_ne_one k hk hk0 h := itE_ne_one (Nat.pos_of_ne_zero hk0) hk (by
    rw [← coe_iota, h]
    rfl)
  iota_z₁ := Subtype.ext (by rw [coe_iota, itE_45]; rfl)
  halves k _ := by rw [coe_iota]; exact itE_blocks_iff k
  cent hP x hx := by
    obtain ⟨k, hk, e⟩ := cent_le hP x.2 fun i hi => congrArg Subtype.val (hx i hi)
    exact ⟨k, hk, Subtype.ext (by rw [coe_iota, ← e])⟩
  norm w hw i hi := by
    obtain ⟨l, hl, rfl⟩ := normGens_mem hw
    refine ⟨aCode.getD (6 * l + i) 0, aCode_lt _ (by omega), ?_⟩
    rw [coe_uElem, coe_iota]
    exact mul_inv_eq_of_eq_mul (norm_rel hl hi)
  fuse kv hkv kw hkw hv0 hv16 hw0 hw16 ht := by
    rw [coe_iota, coe_iota]
    exact fuse_pair hkv hkw hv0 hv16 hw0 hw16 ht
  conj_z₁ hP k hk g hg e := by
    rw [coe_iota] at e
    exact conj_type hP hk hg e

end CFSG.KD.HN1408.AK

end

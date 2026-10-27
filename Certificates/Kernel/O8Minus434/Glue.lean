module

public import Certificates.Kernel.O8Minus434.Checks
public import Certificates.Kernel.OmegaEight.Bridge3002
public import CFSG.Certificates.Kernel.U62PairMat

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8M434

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelO8
open CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus CFSG.EvenSmallLie.OmegaEightMinus
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight (pushWords wordsOf)

theorem allLt_true {n : Nat} {p : Nat → Bool} :
    CFSG.Monster.B.Co2.Native.allLt n p = true ↔ ∀ i < n, p i = true := by
  unfold CFSG.Monster.B.Co2.Native.allLt
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  exact ⟨fun h i hi => h ⟨i, hi⟩ (List.mem_finRange _), fun h i _ => h i i.2⟩

theorem fget_lt8 (X i : Nat) : CFSG.KLie.CT.fget X i 8 < 2 ^ 8 := by
  rw [CFSG.KC.U62P.Snd.fget_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos 8)

theorem fget_pg8 (X i : Nat) : CFSG.KLie.CT.fget X i 8 = pg 8 255 X i :=
  CFSG.KC.O8.PA.fget_eq_pg X i 8

theorem eqA_refl136 (t : Array Nat) : eqA 136 t t = true := by
  unfold eqA
  rw [allLt_true]
  intro i _
  simp

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem linArr_eq {cols : List Nat} (h : linLtK NSM cols = true) :
    linArr cols = unpack 136 8 (linK NSM NIM cols) := by
  have hb := (CFSG.KC.O8.PA.ctAllN_iff).1 h
  unfold linArr unpack
  congr 1
  funext i
  have hi := i.2
  have hl : linApply cols (pg 8 255 NSM i.val) < 256 := by
    have := hb i.val hi
    rwa [Nat.blt_eq, fget_pg8] at this
  have hc : ∀ k, nsMap NSM NIM (linApply cols) k < 2 ^ 8 := fun k => fget_lt8 _ _
  rw [← CFSG.KC.O8.PA.fget_eq_pg, linK, CFSG.KC.U62P.Snd.fget_orN hc, if_pos hi]
  unfold nsMap
  rw [fget_pg8, fget_pg8, ns_bindM i.val hi, ni_bindM _ hl]

theorem mem_z {i : Nat} (hi : i < 3) : zCols.getD i [] ∈ allCols := by
  interval_cases i <;> decide

theorem mem_s {k : Nat} (hk : k < 3) : sCols.getD k [] ∈ allCols := by
  interval_cases k <;> decide

theorem mem_t : tCols ∈ allCols := by decide

theorem sArrs_get {k : Nat} (hk : k < 3) : sArrs[k]! = linArr (sCols.getD k []) := by
  interval_cases k <;> rfl

theorem elt_ok {c : List Nat} (hc : c ∈ allCols) :
    linArr c = unpack 136 8 (linK NSM NIM c) ∧ cnM (linK NSM NIM c) = true ∧
      pmM (linK NSM NIM c) = true ∧ cnM (pinvM (linK NSM NIM c)) = true ∧
      memOK (linArr c) = true := by
  have hl := List.all_eq_true.1 kLin c hc
  have he := List.all_eq_true.1 kElt c hc
  unfold eltK at he
  simp only [bAnd_iff] at he
  obtain ⟨hcn, hpm, hci, hs⟩ := he
  have e := linArr_eq hl
  refine ⟨e, hcn, hpm, hci, ?_⟩
  have hG : Nat.shiftRight (linK NSM NIM c) (136 * 8) = 0 := by
    have h' := hcn
    unfold cnM canonK at h'
    simp only [bAnd_iff] at h'
    exact Nat.eq_of_beq_eq_true h'.2.1
  unfold memOK omegaLevels
  rw [e, isInvA_ofM hpm,
    siftK_eq bindsOmM (perm_of_head OmM.head) OmM.hl rfl hG (range_of_permOK hpm)]
  simpa using hs

theorem z_ok {i : Nat} (hi : i < 3) : zArr i = unpack 136 8 (ZK i) ∧ cnM (ZK i) = true :=
  ⟨(elt_ok (mem_z hi)).1, (elt_ok (mem_z hi)).2.1⟩

theorem t_ok : tArr = unpack 136 8 TK ∧ cnM TK = true ∧ pmM TK = true ∧ cnM (pinvM TK) = true :=
  ⟨(elt_ok mem_t).1, (elt_ok mem_t).2.1, (elt_ok mem_t).2.2.1, (elt_ok mem_t).2.2.2.1⟩

theorem s_ok {k : Nat} (hk : k < 3) : sArrs[k]! = unpack 136 8 (SK k) ∧ cnM (SK k) = true := by
  rw [sArrs_get hk]
  exact ⟨(elt_ok (mem_s hk)).1, (elt_ok (mem_s hk)).2.1⟩

theorem elts_k : eltsCheck = true := by
  unfold eltsCheck
  simp only [Bool.and_eq_true, allLt_true]
  refine ⟨⟨fun i hi => (elt_ok (mem_z hi)).2.2.2.2, (elt_ok mem_t).2.2.2.2⟩, fun k hk => ?_⟩
  rw [sArrs_get hk]
  exact (elt_ok (mem_s hk)).2.2.2.2

theorem cn_pow {i a : Nat} (hi : i < 3) (ha : a < 3) : cnM (ppwM (ZK i) a) = true :=
  allN_spec (allN_spec kPow i hi) a ha

theorem vec_eq {a b c : Nat} (ha : a < 3) (hb : b < 3) (hc : c < 3) :
    vecArr a b c = unpack 136 8 (vK a b c) ∧ cnM (vK a b c) = true := by
  have h0 := z_ok (by norm_num : 0 < 3)
  have h1 := z_ok (by norm_num : 1 < 3)
  have h2 := z_ok (by norm_num : 2 < 3)
  have c0 := cn_pow (by norm_num : 0 < 3) ha
  have c1 := cn_pow (by norm_num : 1 < 3) hb
  have c2 := cn_pow (by norm_num : 2 < 3) hc
  unfold vecArr
  rw [h0.1, h1.1, h2.1, powArr_pcM h0.2, powArr_pcM h1.2, powArr_pcM h2.2, compA_pcM c0 c1,
    compA_pcM (cn_pcM c0 c1) c2]
  exact ⟨rfl, cn_pcM (cn_pcM c0 c1) c2⟩

theorem not_beq_iff {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : Nat.beq a b = false := by
  revert h
  cases Nat.beq a b <;> simp

theorem wreath_k : wreathCheck = true := by
  have h := kWreath
  simp only [bAnd_iff] at h
  obtain ⟨w1, w2, w3, w4, w5⟩ := h
  obtain ⟨et, ct, pt, cti⟩ := t_ok
  unfold wreathCheck
  simp only [Bool.and_eq_true, allLt_true]
  refine ⟨⟨⟨⟨⟨fun i hi => ?_, fun i hi j hj => ?_⟩, ?_⟩, fun i hi => ?_⟩, fun a ha b hb c hc => ?_⟩,
    fun a ha b hb c hc => ?_⟩
  · rw [(z_ok hi).1, powArr_pcM (z_ok hi).2, Nat.eq_of_beq_eq_true (allN_spec w1 i hi), idA_eqM]
    exact eqA_refl136 _
  · rw [(z_ok hi).1, (z_ok hj).1, commArr_pcM (z_ok hi).2 (z_ok hj).2]
    exact allN_spec (allN_spec w2 i hi) j hj
  · rw [et, powArr_pcM ct, Nat.eq_of_beq_eq_true w3, idA_eqM]
    exact eqA_refl136 _
  · have e : cjM TK (ZK i) = ZK ((i + 1) % 3) := Nat.eq_of_beq_eq_true (allN_spec w4 i hi)
    rw [et, (z_ok hi).1, (z_ok (Nat.mod_lt _ (by norm_num))).1, conjArr_cjM ct cti pt (z_ok hi).2, e]
    exact eqA_refl136 _
  · have hv := allN_spec (allN_spec (allN_spec w5 a ha) b hb) c hc
    simp only [bAnd_iff] at hv
    obtain ⟨ev, cv⟩ := vec_eq ha hb hc
    rw [ev, idA_eqM, eqA_pcM cv kPidM'.1]
    rcases Nat.eq_zero_or_pos (a + (b + c)) with h0 | h0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hc0 : c = 0 := by omega
      subst ha0 hb0 hc0
      rfl
    · have hz : Nat.beq (Nat.add a (Nat.add b c)) 0 = false := beq_false_of_ne (by
        change a + (b + c) ≠ 0
        omega)
      rw [hz] at hv
      have := not_beq_iff hv.1
      simp [this]
  · have hv := allN_spec (allN_spec (allN_spec w5 a ha) b hb) c hc
    simp only [bAnd_iff] at hv
    obtain ⟨ev, cv⟩ := vec_eq ha hb hc
    rw [ev, et, eqA_pcM cv ct, not_beq_iff hv.2]
    rfl

theorem cent_k : centCheck = true := by
  have h := kCent
  simp only [bAnd_iff] at h
  obtain ⟨c1, c2⟩ := h
  unfold centCheck
  simp only [Bool.and_eq_true, allLt_true, Bool.or_eq_true]
  refine ⟨fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [(s_ok hk).1, powArr_pcM (s_ok hk).2, Nat.eq_of_beq_eq_true (allN_spec c1 k hk), idA_eqM]
    exact eqA_refl136 _
  · have hv := allN_spec (allN_spec c2 k hk) i hi
    by_cases e : i = k
    · left
      simp [e]
    · right
      have hne : Nat.beq i k = false := beq_false_of_ne e
      rw [hne] at hv
      rw [(s_ok hk).1, (z_ok hi).1, commArr_pcM (s_ok hk).2 (z_ok hi).2]
      exact hv

theorem sGens : sArrs.size = 3 ∧ ∀ j < 3, sArrs[j]! = unpack 136 8 (G.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [(s_ok hj).1, Nat.eq_of_beq_eq_true (allN_spec kGenS j hj)]

theorem bindsG : Binds 136 8 G.S 18 7 G.BP genS ((genBase.map Fin.val).toArray) := by
  obtain ⟨hs, he⟩ := pushWords_eq sGens G.head
  refine ⟨by norm_num, by norm_num, by norm_num, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem chain_k : genChainCheck = true := by
  unfold genChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsG G.head G.hl (by decide) G.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsG (perm_of_head G.head) G.hl]
  decide +kernel

open Certificates in
open CFSG.RankThree.PartTwo.Sec4.Item434OmegaMinus in
theorem cert8096 : eltsCheck = true ∧ wreathCheck = true ∧ centCheck = true ∧ genChainCheck = true := ⟨elts_k, wreath_k, cent_k, chain_k⟩

end CertificateChecks.KernelO8M434

end

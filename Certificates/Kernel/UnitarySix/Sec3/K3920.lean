module

public import Certificates.Kernel.UnitarySix.Sec3.K3920Chk
public import Certificates.Kernel.UnitarySix.Sec3.K3607
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.RankThree.F2Perm

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU6.Sec3

open CFSG.KC.U6Sec3 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Enum CFSG.Monster.B.Co2.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.EvenSmallLie.UnitarySix.YamadaHAut
open CFSG.RankThree.Native
open CFSG.Monster.B.Co2 (allLt_iff)

theorem labA4_k : labA4Check = true := by
  unfold labA4Check
  rw [Bool.and_eq_true]
  refine ⟨by decide, ?_⟩
  rw [chA4_K.O_all]
  refine List.all_eq_true.2 fun j hj => allLt_iff.2 fun p hp => ?_
  have hj' := PermK.canon (chA4_P j (List.mem_range.1 hj))
  rw [unpack_get hp, labA4_eq _ (canon_lt hj' hp), labA4_eq _ hp]
  exact allN_spec (List.all_eq_true.1 kLabA4 j hj) p hp

theorem commPt_of {X Y : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
    (hY : canonK 693 10 (mask 10) (693 * 10) Y = true) (h : commPtK X Y = true) :
    eqA 693 (compA 693 (unpack 693 10 Y) (unpack 693 10 X))
      (compA 693 (unpack 693 10 X) (unpack 693 10 Y)) = true := by
  rw [comp_unpack hY hX, comp_unpack hX hY, eqA, allLt_iff]
  intro i hi
  rw [unpack_get hi, unpack_get hi, comp_get hY hX hi, comp_get hX hY hi, beq_iff_eq]
  exact (Nat.eq_of_beq_eq_true (allN_spec h i hi)).symm

theorem mem_filtC {X : ℕ} : ∀ {C : List ℕ} {Y : ℕ}, Y ∈ filtC X C → Y ∈ C ∧ commPtK X Y = true
  | [], Y, h => by simp [filtC] at h
  | Z :: C, Y, h => by
    have e : filtC X (Z :: C) = Bool.rec (filtC X C) (Z :: filtC X C) (commPtK X Z) := rfl
    rw [e] at h
    cases hz : commPtK X Z
    · rw [hz] at h
      exact ⟨List.mem_cons_of_mem _ (mem_filtC h).1, (mem_filtC h).2⟩
    · rw [hz] at h
      rcases List.mem_cons.1 h with rfl | h'
      · exact ⟨List.mem_cons_self, hz⟩
      · exact ⟨List.mem_cons_of_mem _ (mem_filtC h').1, (mem_filtC h').2⟩

theorem movesK_spec {p : ℕ} : ∀ {CS : List ℕ}, movesK CS p = true →
    ∃ Y ∈ CS, pg 10 (mask 10) Y p ≠ p
  | [], h => by simp [movesK] at h
  | Y :: CS, h => by
    have e : movesK (Y :: CS) p = (pg 10 (mask 10) Y p != p || movesK CS p) := rfl
    rw [e, Bool.or_eq_true, bne_iff_ne] at h
    rcases h with h | h
    · exact ⟨Y, List.mem_cons_self, h⟩
    · obtain ⟨Z, hZ, hz⟩ := movesK_spec h
      exact ⟨Z, List.mem_cons_of_mem _ hZ, hz⟩

theorem qF_lt' : ∀ k < 5, ∀ j ∈ qF[k]!, j < 18 := by decide

theorem l1_of {X : ℕ} (hX : canonK 693 10 (mask 10) (693 * 10) X = true)
    (h : l1K (l1Words.map wK).reverse X = true) : l1At (unpack 693 10 X) = true := by
  unfold l1K at h
  unfold l1At
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (by rw [eq_id hX]; exact h))
  · refine Or.inl (Or.inr ?_)
    obtain ⟨k, hk, hq⟩ := List.any_eq_true.1 h
    have hk' := List.mem_range.1 hk
    rw [strictB_eq, strictB_eq, Bool.and_eq_true] at hq
    refine List.any_eq_true.2 ⟨k, hk, ?_⟩
    rw [Bool.and_eq_true, CFSG.RankThree.Native.F2.validA_of_rep (rep_wA tabs_k _ (qF_lt' k hk')),
      (wK_spec (qF_lt' k hk')).1, hG 14 (by norm_num),
      conjInv_unpack hq.1 (hc 14 (by norm_num)),
      eq_unpack hX (canon_comp (PermK.canon_inv hq.1) (canon_comp (hc 14 (by norm_num))
        (PermK.canon hq.1)))]
    exact ⟨rfl, hq.2⟩
  · right
    rw [forceL_eq, List.append_nil] at h
    unfold noCommonFix
    refine allLt_iff.2 fun p hp => ?_
    obtain ⟨Y, hY, hm⟩ := movesK_spec (allN_spec h p hp)
    obtain ⟨hYC, hc'⟩ := mem_filtC (List.mem_reverse.1 hY)
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hYC)
    have hwl := l1W_lt w hw
    refine List.any_eq_true.2 ⟨wA w, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨List.mem_map.2 ⟨w, hw, rfl⟩, ?_⟩
      rw [(wK_spec hwl).1]
      exact commPt_of hX (wK_spec hwl).2 hc'
    · rw [(wK_spec hwl).1, unpack_get hp, bne_iff_ne]
      exact hm

end CertificateChecks.KernelU6.Sec3

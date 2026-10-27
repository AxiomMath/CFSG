module

public import Certificates.Kernel.HN1408.Tab6CntChk
public import Certificates.Kernel.HN1408.TabXCntFacts
public import Certificates.Kernel.HN1408.W441872Glue
public import Certificates.Kernel.HN1408.TableIShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab6Check

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Tab6

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408 CFSG.KD.HN1408.CzT
open CFSG.KD.HN1408.TabX CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model CFSG.EvenSporadicStandard.HNRecog.Section3

theorem band3_iff (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem beq_iff {H : Nat} {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) {i j x : Nat}
    (hi : i < 1280) (hj : j < 24) (hx : x < 1408) :
    Nat.beq (pt (T0 i) (pt (T1 j) (pt H x))) (pt H (pt (T0 i) (pt (T1 j) x))) = true ↔
      ((t0P i * t1P j) * h) ⟨x, hx⟩ = (h * (t0P i * t1P j)) ⟨x, hx⟩ := by
  have hy : pt H x < 1408 := pt_lt hH.1 hx
  have hgx : pt (T0 i) (pt (T1 j) x) < 1408 := by rw [ev_eq hi hj hx]; exact Fin.isLt _
  have hfx : (⟨pt H x, hy⟩ : Fin 1408) = h ⟨x, hx⟩ := Fin.ext (repC_pt hH hx)
  have hfg : (⟨pt (T0 i) (pt (T1 j) x), hgx⟩ : Fin 1408) = (t0P i * t1P j) ⟨x, hx⟩ :=
    Fin.ext (ev_eq hi hj hx)
  rw [ev_eq hi hj hy, repC_pt hH hgx, hfx, hfg]
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro hb
    exact Fin.ext (Nat.eq_of_beq_eq_true hb)
  · intro he
    rw [he]
    exact Nat.beq_refl _

theorem comm3_iff {H : Nat} {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) {i j : Nat}
    (hi : i < 1280) (hj : j < 24) :
    comm3 (T0 i) (T1 j) H = true ↔
      (((t0P i * t1P j) * h) ⟨0, by norm_num⟩ = (h * (t0P i * t1P j)) ⟨0, by norm_num⟩ ∧
        ((t0P i * t1P j) * h) ⟨1, by norm_num⟩ = (h * (t0P i * t1P j)) ⟨1, by norm_num⟩) ∧
        ((t0P i * t1P j) * h) ⟨2, by norm_num⟩ = (h * (t0P i * t1P j)) ⟨2, by norm_num⟩ := by
  unfold comm3 commB
  rw [band3_iff, band3_iff, beq_iff hH hi hj (by norm_num : (0 : Nat) < 1408),
    beq_iff hH hi hj (by norm_num : (1 : Nat) < 1408),
    beq_iff hH hi hj (by norm_num : (2 : Nat) < 1408)]

theorem card_le_of_stab3K (hP : Nat.card ↥P1408 = 177408000) {H n : Nat}
    {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) (hk : stab3K H n = true) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408)))) ≤ n := by
  have hc : stab3Cnt H = n := Nat.eq_of_beq_eq_true hk
  unfold stab3Cnt at hc
  rw [strictN_eq'] at hc
  have hQ := ncard_eq_czCnt hP (F := fun A B => comm3 A B H)
    (Q := fun g => ((g * h) ⟨0, by norm_num⟩ = (h * g) ⟨0, by norm_num⟩ ∧
      (g * h) ⟨1, by norm_num⟩ = (h * g) ⟨1, by norm_num⟩) ∧
      (g * h) ⟨2, by norm_num⟩ = (h * g) ⟨2, by norm_num⟩)
    (fun i hi j hj => comm3_iff hH hi hj)
  rw [hc] at hQ
  have hcard : Nat.card ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408)))) =
      ((P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({h} : Set (Equiv.Perm (Fin 1408))) : Subgroup (Equiv.Perm (Fin 1408))) :
          Set (Equiv.Perm (Fin 1408))).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, ← hQ]
  refine Set.ncard_le_ncard (fun g hg => ?_) (Set.toFinite _)
  rw [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff] at hg
  refine ⟨hg.1, ⟨?_, ?_⟩, ?_⟩ <;> rw [hg.2]

theorem repC_row {r : OrbRow} (hl : lettersOK (r.conj ++ wordAZ ++ r.conj.reverse) = true)
    (hc : lettersOK r.conj = true) :
    RepC (WK (r.conj ++ wordAZ ++ r.conj.reverse)) (r.repElem wordAZ) := by
  have e : r.repElem wordAZ = elemW (r.conj ++ wordAZ ++ r.conj.reverse) := by
    rw [elemW_append, elemW_append, W441872.elemW_rev hc]
    rfl
  rw [e]
  exact repC_word hl

theorem cent_wordAZ :
    P1408 ⊓ centralizer ({elemW wordAZ} : Set (Equiv.Perm (Fin 1408))) =
      P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  rw [W441872.elemW_wordAZ]
  exact cent_az basic_ab.2.2.1

@[expose] def tab6N : Fin 8 → Nat := ![384, 1024, 48, 64, 32, 240, 20, 16]

theorem stab3K_row (i : Fin 8) :
    stab3K (WK ((tab6Row i).conj ++ wordAZ ++ (tab6Row i).conj.reverse)) (tab6N i) = true := by
  fin_cases i
  · exact ch441694_s0
  · exact ch441694_s1
  · exact ch441694_s2
  · exact ch441694_s3
  · exact ch441694_s4
  · exact ch441694_s5
  · exact ch441694_s6
  · exact ch441694_s7

theorem letters_row (i : Fin 8) :
    lettersOK ((tab6Row i).conj ++ wordAZ ++ (tab6Row i).conj.reverse) = true ∧
      lettersOK (tab6Row i).conj = true := by
  fin_cases i <;> exact ⟨by decide, by decide⟩

theorem tab6_stab_le (hP : Nat.card ↥P1408 = 177408000) (i : Fin 8) :
    Nat.card ↥(Gx (wordP wordAZ) ⊓ Gx ((tab6Row i).rowP wordAZ)) ≤ tab6N i := by
  rw [natCard_inf_Gx_subtype P1408 (wordP wordAZ) ((tab6Row i).rowP wordAZ), coe_wordP,
    coe_rowP, cent_wordAZ]
  exact card_le_of_stab3K hP (repC_row (letters_row i).1 (letters_row i).2) (stab3K_row i)

end CFSG.KD.HN1408.Tab6

end

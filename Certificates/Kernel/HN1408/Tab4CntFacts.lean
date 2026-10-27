module

public import Certificates.Kernel.HN1408.Tab4CntChk
public import Certificates.Kernel.HN1408.CbTFacts
public import Certificates.Kernel.HN1408.W441872Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Check

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CbT

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408 CFSG.KD.HN1408.Tr2
open CFSG.EvenSporadicStandard.HNRecog
open CFSG.EvenSporadicStandard.HNRecog.Section3Model CFSG.EvenSporadicStandard.HNRecog.Section3

theorem band2_iff (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem beq_iff {H : Nat} {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) {i j x : Nat}
    (hi : i < 672) (hj : j < 120) (hx : x < 1408) :
    Nat.beq (pt (T0 i) (pt (T1 j) (pt H x))) (pt H (pt (T0 i) (pt (T1 j) x))) = true ↔
      ((t0Q i * t1Q j) * h) ⟨x, hx⟩ = (h * (t0Q i * t1Q j)) ⟨x, hx⟩ := by
  have hy : pt H x < 1408 := pt_lt hH.1 hx
  have hgx : pt (T0 i) (pt (T1 j) x) < 1408 := by rw [ev_eq hi hj hx]; exact Fin.isLt _
  have hfx : (⟨pt H x, hy⟩ : Fin 1408) = h ⟨x, hx⟩ := Fin.ext (repC_pt hH hx)
  have hfg : (⟨pt (T0 i) (pt (T1 j) x), hgx⟩ : Fin 1408) = (t0Q i * t1Q j) ⟨x, hx⟩ :=
    Fin.ext (ev_eq hi hj hx)
  rw [ev_eq hi hj hy, repC_pt hH hgx, hfx, hfg]
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro hb
    exact Fin.ext (Nat.eq_of_beq_eq_true hb)
  · intro he
    rw [he]
    exact Nat.beq_refl _

theorem comm2_iff {H : Nat} {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) {i j : Nat}
    (hi : i < 672) (hj : j < 120) :
    comm2 1401 (T0 i) (T1 j) H = true ↔
      ((t0Q i * t1Q j) * h) ⟨0, by norm_num⟩ = (h * (t0Q i * t1Q j)) ⟨0, by norm_num⟩ ∧
        ((t0Q i * t1Q j) * h) ⟨1401, by norm_num⟩ = (h * (t0Q i * t1Q j)) ⟨1401, by norm_num⟩ := by
  unfold comm2
  rw [band2_iff, beq_iff hH hi hj (by norm_num : (0 : Nat) < 1408),
    beq_iff hH hi hj (by norm_num : (1401 : Nat) < 1408)]

theorem card_le_of_stab2K (hP : Nat.card ↥P1408 = 177408000) {H n : Nat}
    {h : Equiv.Perm (Fin 1408)} (hH : RepC H h) (hk : stab2K H n = true) :
    Nat.card ↥(P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408)))) ≤ n := by
  have hc : stab2Cnt H = n := Nat.eq_of_beq_eq_true hk
  unfold stab2Cnt at hc
  rw [TabX.strictN_eq'] at hc
  have hQ := ncard_eq_cnt2 hP (F := fun A B => comm2 1401 A B H)
    (Q := fun g => (g * h) ⟨0, by norm_num⟩ = (h * g) ⟨0, by norm_num⟩ ∧
      (g * h) ⟨1401, by norm_num⟩ = (h * g) ⟨1401, by norm_num⟩)
    (fun i hi j hj => comm2_iff hH hi hj)
  rw [hc] at hQ
  have hcard : Nat.card ↥(P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ⊓
      centralizer ({h} : Set (Equiv.Perm (Fin 1408)))) =
      ((P1408 ⊓ centralizer ({elemW wordB} : Set (Equiv.Perm (Fin 1408))) ⊓
        centralizer ({h} : Set (Equiv.Perm (Fin 1408))) : Subgroup (Equiv.Perm (Fin 1408))) :
          Set (Equiv.Perm (Fin 1408))).ncard :=
    Nat.card_coe_set_eq _
  rw [hcard, ← hQ]
  refine Set.ncard_le_ncard (fun g hg => ?_) (Set.toFinite _)
  rw [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff] at hg
  refine ⟨hg.1, ?_, ?_⟩ <;> rw [hg.2]

theorem repC_rowB {r : OrbRow} (hl : lettersOK (r.conj ++ wordB ++ r.conj.reverse) = true)
    (hc : lettersOK r.conj = true) :
    RepC (WK (r.conj ++ wordB ++ r.conj.reverse)) (r.repElem wordB) := by
  have e : r.repElem wordB = elemW (r.conj ++ wordB ++ r.conj.reverse) := by
    rw [elemW_append, elemW_append, W441872.elemW_rev hc]
    rfl
  rw [e]
  exact repC_word hl

@[expose] def tab4N : Fin 6 → Nat := ![768, 768, 1440, 64, 240, 240]

theorem stab2K_row (i : Fin 6) :
    stab2K (WK ((tab4Row i).conj ++ wordB ++ (tab4Row i).conj.reverse)) (tab4N i) = true := by
  fin_cases i
  · exact ch441693_s0
  · exact ch441693_s1
  · exact ch441693_s2
  · exact ch441693_s3
  · exact ch441693_s4
  · exact ch441693_s5

theorem letters_row (i : Fin 6) :
    lettersOK ((tab4Row i).conj ++ wordB ++ (tab4Row i).conj.reverse) = true ∧
      lettersOK (tab4Row i).conj = true := by
  fin_cases i <;> exact ⟨by decide, by decide⟩

theorem tab4_stab_le (hP : Nat.card ↥P1408 = 177408000) (i : Fin 6) :
    Nat.card ↥(Gx (wordP wordB) ⊓ Gx ((tab4Row i).rowP wordB)) ≤ tab4N i := by
  rw [natCard_inf_Gx_subtype P1408 (wordP wordB) ((tab4Row i).rowP wordB), coe_wordP, coe_rowP]
  exact card_le_of_stab2K hP (repC_rowB (letters_row i).1 (letters_row i).2) (stab2K_row i)

end CFSG.KD.HN1408.CbT

end

module

public import Certificates.Kernel.HN1408.XCentChk
public import Certificates.Kernel.HN1408.CzTScan
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.XCent

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

abbrev nC : Subgroup (Equiv.Perm (Fin 1408)) :=
  closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408)))

theorem and4 {a b c d : Bool} (h : bAnd(a, bAnd(b, bAnd(c, d))) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem head_gen {Z C₁ C₂ A B : Nat}
    (h : (strictB Z fun Z => strictB C₁ fun C₁ => strictB C₂ fun C₂ =>
      bAnd(Nat.beq C₁ A, bAnd(Nat.beq C₂ B, bAnd(commP C₁ Z, commP C₂ Z)))) = true) :
    C₁ = A ∧ C₂ = B ∧ commP C₁ Z = true ∧ commP C₂ Z = true := by
  simp only [Orb.strictB_eq] at h
  obtain ⟨a, b, c, d⟩ := and4 h
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c, d⟩

theorem head_parts :
    CT 0 = WK xC1 ∧ CT 1 = WK xC2 ∧ commP (CT 0) (WK wordZ) = true ∧
      commP (CT 1) (WK wordZ) = true := by
  have h := head_ok
  rw [xcHead.eq_1] at h
  exact head_gen h

theorem repC_c1 : RepC (CT 0) (elemW xC1) := by
  rw [head_parts.1]
  exact repC_word (by decide)

theorem repC_c2 : RepC (CT 1) (elemW xC2) := by
  rw [head_parts.2.1]
  exact repC_word (by decide)

theorem c1_mem : elemW xC1 ∈ nC := subset_closure (by simp)

theorem c2_mem : elemW xC2 ∈ nC := subset_closure (by simp)

theorem sub2_mem (i : Nat) : ∃ s ∈ nC, RepC (sub2 (CT 0) (CT 1) i) s := by
  unfold sub2
  cases h1 : Nat.beq i 1
  · cases h2 : Nat.beq i 2
    · exact ⟨1, one_mem _, repC_idK⟩
    · exact ⟨_, c2_mem, repC_c2⟩
  · exact ⟨_, c1_mem, repC_c1⟩

theorem foldr_mem (W : Nat) : ∀ L : List Nat, ∃ g ∈ nC,
    RepC (L.foldr (fun k acc => pc (sub2 (CT 0) (CT 1) (fd2 W k)) acc) idK) g
  | [] => ⟨1, one_mem _, repC_idK⟩
  | k :: L => by
    obtain ⟨g, hg, hr⟩ := foldr_mem W L
    obtain ⟨s, hs, hsr⟩ := sub2_mem (fd2 W k)
    exact ⟨s * g, mul_mem hs hg, repC_pc hsr hr⟩

theorem pwK_mem (W : Nat) : ∃ g ∈ nC, RepC (pwK (CT 0) (CT 1) W) g := by
  unfold pwK
  rw [Orb.foldN_eq]
  exact foldr_mem W _

theorem words_gen {Et : Nat → Nat} {C₁ C₂ : Nat} {Wd : Nat → Nat}
    (h : (strictB C₁ fun C₁ => strictB C₂ fun C₂ =>
      allN 46 fun k => Nat.beq (Et k) (pwK C₁ C₂ (Wd k))) = true) {k : Nat} (hk : k < 46) :
    Et k = pwK C₁ C₂ (Wd k) := by
  simp only [Orb.strictB_eq] at h
  exact Nat.eq_of_beq_eq_true (allN_spec h k hk)

theorem words_parts {k : Nat} (hk : k < 46) : E k = pwK (CT 0) (CT 1) (Wd k) := by
  have h := words_ok
  rw [xcWords.eq_1] at h
  exact words_gen h hk

theorem e_mem {k : Nat} (hk : k < 46) : ∃ g ∈ nC, RepC (E k) g := by
  rw [words_parts hk]
  exact pwK_mem _

noncomputable def eP (k : Nat) : Equiv.Perm (Fin 1408) :=
  if hk : k < 46 then (e_mem hk).choose else 1

theorem eP_spec {k : Nat} (hk : k < 46) : eP k ∈ nC ∧ RepC (E k) (eP k) := by
  unfold eP
  rw [dif_pos hk]
  exact (e_mem hk).choose_spec

theorem comm_of_commP {X Y : Nat} {g h : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y h)
    (hc : commP X Y = true) : g * h = h * g := by
  have e := Nat.eq_of_beq_eq_true hc
  have h1 := repC_pc hX hY
  rw [e] at h1
  exact eq_of_repC h1 (repC_pc hY hX)

theorem eq_of_beq_pc {X Y U V : Nat} {x y u v : Equiv.Perm (Fin 1408)} (hX : RepC X x)
    (hY : RepC Y y) (hU : RepC U u) (hV : RepC V v) (h : Nat.beq (pc X Y) (pc U V) = true) :
    x * y = u * v := by
  have h1 := repC_pc hX hY
  rw [Nat.eq_of_beq_eq_true h] at h1
  exact eq_of_repC h1 (repC_pc hU hV)

theorem nC_le : nC ≤ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := by
  have hz : RepC (WK wordZ) elemZ := repC_word (by decide)
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact mem_cent_of repC_c1 (elemW_mem _) head_parts.2.2.1
  · exact mem_cent_of repC_c2 (elemW_mem _) head_parts.2.2.2

theorem center_gen {Et : Nat → Nat} {C₁ C₂ : Nat}
    (h : (strictB C₁ fun C₁ => strictB C₂ fun C₂ =>
      allN 8 fun k => bAnd(commP (Et k) C₁, commP (Et k) C₂)) = true) {k : Nat} (hk : k < 8) :
    commP (Et k) C₁ = true ∧ commP (Et k) C₂ = true := by
  simp only [Orb.strictB_eq] at h
  exact mkA (allN_spec h k hk)

theorem center_parts {k : Nat} (hk : k < 8) :
    commP (E k) (CT 0) = true ∧ commP (E k) (CT 1) = true := by
  have h := center_ok
  rw [xcCenter.eq_1] at h
  exact center_gen h hk

theorem center_eP {k : Nat} (hk : k < 8) :
    eP k * elemW xC1 = elemW xC1 * eP k ∧ eP k * elemW xC2 = elemW xC2 * eP k := by
  have hs := (eP_spec (k := k) (by omega)).2
  exact ⟨comm_of_commP hs repC_c1 (center_parts hk).1,
    comm_of_commP hs repC_c2 (center_parts hk).2⟩

end CFSG.KD.HN1408.XCent

end

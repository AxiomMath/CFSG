module

public import Certificates.Kernel.Sporadic.ONC.CheckWords
public import Certificates.Kernel.Sporadic.ONC.TauGlue
import Certificates.Kernel.Sporadic.ONC.ChainBase

public section

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KS.ONC CFSG.Sporadic.ON CFSG.Sporadic.Th CFSG.Sporadic.Recognition.ONMultiplier

@[expose] noncomputable def onGWG (i : ℕ) : J :=
  wordG (seedG ga gb) (onGW.getD i [])

theorem seedG_neg {G : Type*} [Group G] (gA gB : G) {z : ℤ}
    (hz : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) : seedG gA gB (-z) = (seedG gA gB z)⁻¹ := by
  rcases hz with rfl | rfl | rfl | rfl <;> simp [seedG]

theorem wordG_seedInv {G : Type*} [Group G] (gA gB : G) {w : List ℤ}
    (hw : ∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) :
    wordG (seedG gA gB) (seedInv w) = (wordG (seedG gA gB) w)⁻¹ := by
  unfold wordG seedInv
  rw [List.prod_inv_reverse, List.map_reverse, List.map_map, List.map_map]
  congr 2
  exact List.map_congr_left fun z hz => seedG_neg gA gB (hw z hz)

theorem onGenWords_letters :
    ∀ k < 4, ∀ z ∈ onGenWords.toList.getD k [], z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by
  decide +kernel

theorem onGW_getD :
    ∀ k < 4, onGW.getD k [] = onGenWords.toList.getD k [] ∧
      onGW.getD (k + 4) [] = seedInv (onGenWords.toList.getD k []) := by
  decide +kernel

theorem onGW_seeds : onGW.getD 8 [] = [1] ∧ onGW.getD 9 [] = [2] := by decide +kernel

theorem onGWG_lt {k : ℕ} (hk : k < 4) :
    onGWG k = onG k ∧ onGWG (k + 4) = (onG k)⁻¹ := by
  have e : wordG (seedG ga gb) (onGenWords.toList.getD k []) = onG k := by
    rw [onGenWords_getD, ← genG_eq]
    rfl
  unfold onGWG
  rw [(onGW_getD k hk).1, (onGW_getD k hk).2, wordG_seedInv _ _ (onGenWords_letters k hk), e]
  exact ⟨rfl, rfl⟩

theorem onGWG_letter {z : ℤ} (hz : z.natAbs ≤ 4) :
    onGWG (onLetterIdx z) = onGZ z := by
  unfold onLetterIdx onGZ
  split_ifs with h
  · exact (onGWG_lt (by omega)).1
  · exact (onGWG_lt (by omega)).2

theorem prod_onLetterIdx {w : List ℤ}
    (hw : ∀ z ∈ w, z.natAbs ≤ 4) : ((w.map onLetterIdx).map onGWG).prod = wordG onGZ w := by
  unfold wordG
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun z hz => onGWG_letter (hw z hz)

theorem onCheckPairs_eq :
    ∀ p ∈ onCheckPairs, (p.1.map onGWG).prod = (p.2.map onGWG).prod := by
  have hFA : ∀ c < 154, PV (FA c) := fun c hc =>
    pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsAK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LA ONW.CA
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listA2)) c hc)
  have hFB : ∀ c < 154, PV (FB c) := fun c hc =>
    pv_of_canon (CertificateChecks.KernelSpor.ON.canon_of CertificateChecks.KernelSpor.ON2.colsBK2
      (CertificateChecks.KernelSpor.ON.list_eq ONW.LB ONW.CB
        (CFSG.KS.allN_spec CertificateChecks.KernelSpor.ON2.listB2)) c hc)
  have h := relsK_sound (φ := matJ) (FA := FA) (FB := FB) (gA := ga) (gB := gb) checkWords_ok hFA
    hFB (fun r c => colA r c) (fun r c => colB r c)
  intro p hp
  have hlt : ∀ i ∈ p.1 ++ p.2, i < onGW.length := by
    revert p
    decide +kernel
  exact matJ_injective (h p hp hlt)

theorem natAbs_le_onSurjA : ∀ z ∈ onSurjA, z.natAbs ≤ 4 := by decide +kernel

theorem natAbs_le_onSurjB : ∀ z ∈ onSurjB, z.natAbs ≤ 4 := by decide +kernel

theorem wordG_onCheckWords {w : List ℤ} (hw : w ∈ onCheckWords) :
    wordG onGZ w = 1 := by
  have h := onCheckPairs_eq (w.map onLetterIdx, [])
    (List.mem_append_left _ (List.mem_map.2 ⟨w, hw, rfl⟩))
  rw [prod_onLetterIdx (natAbs_le_of_mem_checkWords hw)] at h
  exact h

theorem wordG_onSurjA : wordG onGZ onSurjA = ga := by
  have h := onCheckPairs_eq (onSurjA.map onLetterIdx, [8])
    (List.mem_append_right _ List.mem_cons_self)
  rw [prod_onLetterIdx natAbs_le_onSurjA] at h
  rw [h, List.map_singleton, List.prod_singleton, onGWG, onGW_seeds.1]
  simp [wordG, seedG]

theorem wordG_onSurjB : wordG onGZ onSurjB = gb := by
  have h := onCheckPairs_eq (onSurjB.map onLetterIdx, [9])
    (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [prod_onLetterIdx natAbs_le_onSurjB] at h
  rw [h, List.map_singleton, List.prod_singleton, onGWG, onGW_seeds.2]
  simp [wordG, seedG]

theorem lift_onGF_rels :
    ∀ r ∈ onRels, FreeGroup.lift onGF (FreeGroup.mk r) = 1 := fun r hr => by
  rw [← wordG_letterZ]
  refine wordG_onCheckWords ?_
  unfold onCheckWords
  exact List.mem_map.2 ⟨r, List.mem_append_left _ hr, rfl⟩

theorem lift_onGF_commWord (i : Fin 4) :
    FreeGroup.lift onGF (FreeGroup.mk (onCommWord i)) = onGF i := by
  have h1 : FreeGroup.lift onGF (FreeGroup.mk ((i, false) :: onCommWord i)) = 1 := by
    rw [← wordG_letterZ]
    refine wordG_onCheckWords ?_
    unfold onCheckWords
    exact List.mem_map.2 ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩),
      rfl⟩
  have e : FreeGroup.mk ((i, false) :: onCommWord i) =
      (FreeGroup.of i)⁻¹ * FreeGroup.mk (onCommWord i) := rfl
  rw [e, map_mul, map_inv, FreeGroup.lift_apply_of, inv_mul_eq_one] at h1
  exact h1.symm

theorem closure_onGF : Subgroup.closure (Set.range onGF) = ⊤ := by
  rw [eq_top_iff, ← closure_gab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · rw [← wordG_onSurjA]; exact wordG_mem natAbs_le_onSurjA
  · rw [← wordG_onSurjB]; exact wordG_mem natAbs_le_onSurjB

end CertificateChecks.KernelSpor.ONC

end

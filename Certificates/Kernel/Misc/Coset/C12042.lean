module

public import CFSG.Sporadic.He.FpSpec
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.Certificates.Kernel.Misc.Coset.MatSound
public import Certificates.Kernel.Misc.Coset.C12042K
public import Certificates.Kernel.Misc.Coset.XG23R
public import CFSG.LieType.Multipliers.G23Data
import all CFSG.LieType.Multipliers.G23Data
import all CFSG.LieType.Multipliers.CoverWords

public section

namespace CertificateChecks.KernelMiscCoset.C12042

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.KC.MiscCoset.Mat CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.G23 CFSG.Sporadic.He.Native

set_option maxRecDepth 100000

@[expose] noncomputable def aM : Matrix (Fin 14) (Fin 14) (ZMod 3) := (aWord.map rootMat).prod

@[expose] noncomputable def bM : Matrix (Fin 14) (Fin 14) (ZMod 3) := (bWord.map rootMat).prod

@[expose] noncomputable def letM : Fin 2 × Bool → Matrix (Fin 14) (Fin 14) (ZMod 3)
  | (0, _) => aM
  | (1, true) => bM
  | (1, false) => bM * bM

@[expose] noncomputable def wordM (w : List (Fin 2 × Bool)) : Matrix (Fin 14) (Fin 14) (ZMod 3) :=
  w.foldr (fun l M => letM l * M) 1

theorem toMat_arrOf (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : toMat 3 14 (arrOf M) = M := by
  ext i j
  rw [toMat_apply, arrOf, getElem!_ofFn _ i.isLt, getElem!_ofFn _ j.isLt]
  exact ZMod.natCast_zmod_val _

theorem toMat_rootProd (js : List (Fin 4)) :
    toMat 3 14 (rootProd js) = (js.map rootMat).prod := by
  induction js with
  | nil => exact toMat_idM 3 14
  | cons j js ih =>
    change toMat 3 14 (mulM 3 14 (rootArr j) (rootProd js)) = _
    rw [toMat_mulM, ih, rootArr, toMat_arrOf, List.map_cons, List.prod_cons]

theorem toMat_letterArr (l : Fin 2 × Bool) : toMat 3 14 (letterArr l) = letM l := by
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s
  · exact toMat_rootProd aWord
  · exact toMat_rootProd aWord
  · change toMat 3 14 (mulM 3 14 bArr bArr) = bM * bM
    rw [toMat_mulM, bArr, toMat_rootProd]
    rfl
  · exact toMat_rootProd bWord

theorem toMat_wordArr (w : List (Fin 2 × Bool)) : toMat 3 14 (wordArr w) = wordM w := by
  induction w with
  | nil => exact toMat_idM 3 14
  | cons l w ih =>
    change toMat 3 14 (mulM 3 14 (letterArr l) (wordArr w)) = _
    rw [toMat_mulM, ih, toMat_letterArr]
    rfl

theorem len_rootL (c : ℕ) : (rootL c).length = 14 := by
  unfold rootL
  split <;> exact length_rows _

theorem len_bL : bL.length = 14 := length_wordL len_rootL _

theorem len_letL (c : ℕ) : (letL c).length = 14 := by
  unfold letL
  split
  · exact length_wordL len_rootL _
  · exact length_wordL len_rootL _
  · exact len_bL
  · exact (length_mulL 3 14 bL bL).trans len_bL

theorem m_root (j : Fin 4) : matL 3 14 (rootL j.val) = rootMat j := by
  fin_cases j <;> exact matL_rows _

theorem matL_roots (js : List (Fin 4)) :
    matL 3 14 (wordL 3 14 rootL (js.map Fin.val)) = (js.map rootMat).prod := by
  rw [matL_wordL len_rootL, List.map_map]
  congr 1
  exact List.map_congr_left fun j _ => m_root j

theorem ma : matL 3 14 aL = aM := matL_roots aWord

theorem mb : matL 3 14 bL = bM := matL_roots bWord

theorem mbi : matL 3 14 biL = bM * bM := by
  unfold biL
  rw [matL_mulL len_bL, mb]

theorem matL_letL (l : Fin 2 × Bool) : matL 3 14 (letL (codeL l)) = letM l := by
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s
  · exact ma
  · exact ma
  · exact mbi
  · exact mb

theorem wordM_eq (w : List (Fin 2 × Bool)) :
    wordM w = matL 3 14 (wordL 3 14 letL (w.map codeL)) := by
  rw [matL_wordL len_letL, List.map_map]
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, ← ih, Function.comp_apply, matL_letL]
    rfl

theorem tR : rels.map encW = CFSG.KBRoute.XG23R.rels := by
  simp [rels, relStrings, relSixString, CFSG.LieType.Multipliers.G23.rep, parseWord, encW,
    CFSG.KBRoute.XG23R.rels]

theorem encW_injective : Function.Injective (encW (m := 2)) := by
  refine List.map_injective_iff.2 fun a b h => ?_
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only [Prod.mk.injEq] at h ⊢
  exact ⟨Fin.ext h.1, h.2⟩

theorem mem_rels {w : List (Fin 2 × Bool)} (h : encW w ∈ CFSG.KBRoute.XG23R.rels) : w ∈ rels := by
  rw [← tR, List.mem_map] at h
  obtain ⟨a, ha, he⟩ := h
  rwa [← encW_injective he]

theorem map_codeL (w : List (Fin 2 × Bool)) : w.map codeL = (encW w).map codeN := by
  rw [encW, List.map_map]
  rfl

theorem model_facts :
    toMat 3 14 aArr * toMat 3 14 aArr = 1 ∧ toMat 3 14 bArr * toMat 3 14 bInvArr = 1 ∧
      (∀ r ∈ rels, toMat 3 14 (wordArr r) = 1) ∧
      (∀ j, toMat 3 14 (wordArr (genWord j)) = rootMat j) ∧
      ∀ i, toMat 3 14 (wordArr (commWords (pairs i))) = toMat 3 14 (letterArr (i, true)) := by
  have ha' : toMat 3 14 aArr = aM := toMat_letterArr (0, true)
  have hb' : toMat 3 14 bArr = bM := toMat_letterArr (1, true)
  have hbi' : toMat 3 14 bInvArr = bM * bM := toMat_letterArr (1, false)
  refine ⟨?_, ?_, fun r hr => ?_, fun j => ?_, fun i => ?_⟩
  · have len_aL : aL.length = 14 := length_wordL len_rootL _
    rw [ha', ← ma, ← matL_mulL len_aL, eq_of_eqM k_aa, matL_idL]
  · have len_biL : biL.length = 14 := (length_mulL 3 14 bL bL).trans len_bL
    rw [hb', hbi', ← mbi, ← mb, ← matL_mulL len_biL, eq_of_eqM k_bb, matL_idL]
  · have hm : encW r ∈ CFSG.KBRoute.XG23R.rels := tR ▸ List.mem_map_of_mem hr
    rw [toMat_wordArr, wordM_eq, map_codeL, eq_of_eqM (List.all_eq_true.1 k_rels _ hm),
      matL_idL]
  · rw [toMat_wordArr, wordM_eq, eq_of_eqM (List.all_eq_true.1 k_gen j (List.mem_finRange j)),
      m_root]
  · rw [toMat_wordArr, wordM_eq, eq_of_eqM (List.all_eq_true.1 k_comm i (List.mem_finRange i)),
      matL_letL, toMat_letterArr]

theorem wR : CFSG.KBRoute.XG23R.T1.words = [encW [((0 : Fin 2), true), (1, true)]] := by
  decide +kernel

theorem pR : (List.replicate 13 [((0 : Fin 2), true), (1, true)]).flatten ∈ rels :=
  mem_rels (by decide +kernel)

theorem card_le : Finite (PG 2 rels) ∧ Nat.card (PG 2 rels) ≤ 4245696 := by
  have h := XG23R.t1
  unfold CFSG.KBRoute.XG23R.T1.ok at h
  have hi := zpowers_index_le_of_tableOk rels tR h (by norm_num) CFSG.KBRoute.XG23R.top _ wR
  exact card_le_of_zpowers_index rels _ (by norm_num) pR hi

end CertificateChecks.KernelMiscCoset.C12042

end

module

public import Certificates.Kernel.McLMult.Facts
public import Certificates.Kernel.McLRels.Tabs
public import CFSG.Certificates.Kernel.Misc.Coset.MemSound
public import CFSG.Sporadic.Recognition.McLMultiplierGlue
public import CFSG.Sporadic.Recognition.CoverTransferWords
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMcLMult

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.LieType.Multipliers CFSG.Certificates
  CFSG.Sporadic.Recognition.McLMultiplier CFSG.Sporadic.Recognition.CoverTransfer

theorem mk_eq_one_of_renumber {S : List (Fin 6)} {w : List (Fin 6 × Bool)}
    {u : List (Fin S.length × Bool)} (hren : renumber S w = some u)
    (h1 : PresentedGroup.mk (wordSet (restrictWords S mclRels)) (FreeGroup.mk u) = 1) :
    PresentedGroup.mk (wordSet mclRels) (FreeGroup.mk w) = 1 := by
  have hf : FreeGroup.lift (fun i => (PresentedGroup.of i : PresentedGroup (wordSet mclRels))) =
      PresentedGroup.mk (wordSet mclRels) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  have hg : ∀ v ∈ mclRels, FreeGroup.lift
      (fun i => (PresentedGroup.of i : PresentedGroup (wordSet mclRels))) (FreeGroup.mk v) = 1 := by
    intro v hv
    rw [hf]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)
  have hrel := lift_restrictWords mclRels S _ hg
  have hψ : (PresentedGroup.toGroup hrel).comp (PresentedGroup.mk _) =
      FreeGroup.lift fun j => (PresentedGroup.of (S.get j) : PresentedGroup (wordSet mclRels)) :=
    FreeGroup.ext_hom _ _ fun j => by
      rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
      exact PresentedGroup.toGroup.of hrel
  have e := DFunLike.congr_fun hψ (FreeGroup.mk u)
  rw [MonoidHom.comp_apply, h1, map_one, lift_mk_map, map_renumber S w u hren, hf] at e
  exact e.symm

theorem mk_eq_one_of_walk {S : List (Fin 6)} (hm : S.length < 128)
    {rels : List (List (ℕ × Bool))} (hrels : (restrictWords S mclRels).map encW = rels)
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S' : ℕ → ℕ} {amap : ℕ}
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h : KB.tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S' amap rels words walk cov =
      true) (htop : KB.topOk amap S.length = true) (hwords : words = [])
    (w : List (Fin 6 × Bool)) (hs : (renumber S w).isSome = true) {cs refs : List ℕ}
    (hc : (encW ((renumber S w).get hs)).map Mem.codeN = cs) (hw : Mem.memOK F nF cs refs = true) :
    PresentedGroup.mk (wordSet mclRels) (FreeGroup.mk w) = 1 := by
  refine mk_eq_one_of_renumber (Option.some_get hs).symm ?_
  have hmem := Mem.memOK_sound (pgGen (restrictWords S mclRels)) (sword_rels _ hrels) h hm htop
    (u := encW ((renumber S w).get hs)) (by
      intro l hl
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
      exact x.1.isLt) (by rw [hc]; exact hw)
  rw [sword_pgGen, hwords, KB.wordSub_nil, Subgroup.mem_bot] at hmem
  exact hmem

abbrev mclIdW (i : Fin 6) : List (Fin 6 × Bool) := (i, false) :: mclCommWord i

theorem relsC_eq : (restrictWords (subsetOf 6 [0, 1, 2, 3, 5]) mclRels).map encW =
    CFSG.KBRoute.F6107c.rels := by
  decide +kernel

theorem relsD_eq : (restrictWords (subsetOf 6 [0, 1, 4]) mclRels).map encW =
    CFSG.KBRoute.F6107d.rels := by
  decide +kernel

theorem wordsC_eq : CFSG.KBRoute.F6107c.T1.words = [] := by decide +kernel

theorem wordsD_eq : CFSG.KBRoute.F6107d.T1.words = [] := by decide +kernel

theorem walk0 : Mem.memOK CFSG.KBData.F6107c.F 39652 [1, 4, 8, 5, 9]
    [15867, 12, 15932, 37, 9] = true := by quickRfl

theorem walk1 : Mem.memOK CFSG.KBData.F6107c.F 39652 [3, 0, 2, 1, 3, 4, 8, 5, 9]
    [15869, 18, 15942, 41, 11, 12, 15932, 37, 9] = true := by quickRfl

theorem walk2 : Mem.memOK CFSG.KBData.F6107c.F 39652
    [5, 2, 0, 3, 1, 8, 4, 2, 4, 2, 5, 3, 5, 9, 3]
    [15871, 26, 78, 16163, 127, 16090, 226, 454, 17764, 17760, 361, 175, 75, 25, 3] = true := by
  quickRfl

theorem walk3 : Mem.memOK CFSG.KBData.F6107c.F 39652
    [7, 2, 4, 3, 5, 2, 6, 4, 2, 4, 7, 3, 5, 3, 5]
    [15873, 15904, 70, 16261, 16769, 666, 1212, 19610, 19606, 17860, 385, 187, 81, 27, 5] =
      true := by
  quickRfl

theorem walk5 : Mem.memOK CFSG.KBData.F6107c.F 39652
    [9, 4, 2, 5, 3, 6, 4, 2, 4, 2, 0, 6, 8, 5, 3, 5, 7, 9, 7, 1, 3]
    [15875, 36, 100, 16429, 17085, 848, 1498, 2506, 23406, 22322, 22312, 22308, 19514, 1275, 17795,
      16843, 311, 149, 61, 19, 3] = true := by
  quickRfl

theorem walk4 : Mem.memOK CFSG.KBData.F6107d.F 72 [5, 2, 0, 4, 0, 3, 1, 5, 1]
    [51, 62, 24, 42, 126, 35, 21, 9, 1] = true := by quickRfl

theorem one_of_walkC {cs refs : List ℕ} (i : Fin 6)
    (hs : (renumber (subsetOf 6 [0, 1, 2, 3, 5]) (mclIdW i)).isSome = true)
    (hc : (encW ((renumber (subsetOf 6 [0, 1, 2, 3, 5]) (mclIdW i)).get hs)).map Mem.codeN = cs)
    (hw : Mem.memOK CFSG.KBData.F6107c.F 39652 cs refs = true) :
    PresentedGroup.mk (wordSet mclRels) (FreeGroup.mk (mclIdW i)) = 1 := by
  have h := CFSG.KBRoute.F6107c.t1
  unfold CFSG.KBRoute.F6107c.T1.ok at h
  exact mk_eq_one_of_walk (by decide) relsC_eq h CFSG.KBRoute.F6107c.top wordsC_eq _ hs hc hw

theorem one_of_walkD {cs refs : List ℕ} (i : Fin 6)
    (hs : (renumber (subsetOf 6 [0, 1, 4]) (mclIdW i)).isSome = true)
    (hc : (encW ((renumber (subsetOf 6 [0, 1, 4]) (mclIdW i)).get hs)).map Mem.codeN = cs)
    (hw : Mem.memOK CFSG.KBData.F6107d.F 72 cs refs = true) :
    PresentedGroup.mk (wordSet mclRels) (FreeGroup.mk (mclIdW i)) = 1 := by
  have h := CFSG.KBRoute.F6107d.t1
  unfold CFSG.KBRoute.F6107d.T1.ok at h
  exact mk_eq_one_of_walk (by decide) relsD_eq h CFSG.KBRoute.F6107d.top wordsD_eq _ hs hc hw

theorem mk_mclCommW (i : Fin 6) :
    PresentedGroup.mk (wordSet mclRels) (mclCommW i) = PresentedGroup.of i := by
  have h1 : PresentedGroup.mk (wordSet mclRels) (FreeGroup.mk (mclIdW i)) = 1 := by
    fin_cases i
    · exact one_of_walkC 0 (by decide +kernel) (by decide +kernel) walk0
    · exact one_of_walkC 1 (by decide +kernel) (by decide +kernel) walk1
    · exact one_of_walkC 2 (by decide +kernel) (by decide +kernel) walk2
    · exact one_of_walkC 3 (by decide +kernel) (by decide +kernel) walk3
    · exact one_of_walkD 4 (by decide +kernel) (by decide +kernel) walk4
    · exact one_of_walkC 5 (by decide +kernel) (by decide +kernel) walk5
  have e : FreeGroup.mk (mclIdW i) = (FreeGroup.of i)⁻¹ * mclCommW i := rfl
  rw [e, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem isPresentation_mclGen :
    IsPresentation mclGen (wordSet mclRels) :=
  isPresentation_mclGen_of mclEvalY_rels mclEvalY_surjA mclEvalY_surjB card_mclCover_le
    three_dvd_orderOf_mclR0 mk_mclCommW

end CertificateChecks.KernelMcLMult

end

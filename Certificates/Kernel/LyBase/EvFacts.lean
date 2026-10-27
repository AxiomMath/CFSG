module

public import Certificates.Kernel.LyBase.Facts
public import Certificates.Kernel.LyBase.EvChk
public import Certificates.Kernel.LyTr.Tr

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyBase

open Equiv CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.YModel.Sem CFSG.KC.MonsterConv.Perm
  CFSG.KC.LyBase CFSG.KC.LyGlue CFSG.KC.LyBenes CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
  CFSG.KS.MulH CFSG.KC.BfsPin CertificateChecks.KernelLy CertificateChecks.KernelLyB CertificateChecks.KernelLyTr
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.Sporadic.Recognition.McLMultiplier

theorem fixC_sound {cs : List Nat} (h : fixC cs = true) :
    cdPtC cL dL cs 0 = 0 ∧ cdPtC cL dL cs 3 = 3 ∧ cdPtC cL dL cs 1 = 1 := by
  have h' : andB (Nat.beq (cdPtC cL dL cs 0) 0) (andB (Nat.beq (cdPtC cL dL cs 3) 3)
      (andB (Nat.beq (cdPtC cL dL cs 1) 1) true)) = true := h
  obtain ⟨h0, h'⟩ := andB_true h'
  obtain ⟨h3, h'⟩ := andB_true h'
  obtain ⟨h1, -⟩ := andB_true h'
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h1⟩

theorem bCodes_eq (r : List (Fin 6 × Bool)) : bCodes r = (wZ (r.map letIdx)).map lcode := by
  rw [bCodes, wZ, List.map_flatMap, show jC = fun j => (jZ j).map lcode from funext jC_eq]

theorem invW_range {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    ∀ l ∈ invW w, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  simp only [invW, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := hw l' hl'
  omega

section Base

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound)
include hc hd hbc

theorem wG_eq_one {z : List ℤ} (hz : ∀ l ∈ z, l ≠ 0 ∧ l.natAbs ≤ 2) (h : fixC (z.map lcode) = true) :
    Ly0.wG Ly0.gens0 z = 1 := by
  obtain ⟨h0, h3, h1⟩ := fixC_sound h
  have e := cdPtC_wG hc hd (cG_mul_cG hc hd) (dG_pow_three hc hd) z hz
  exact eq_one_of_fix_base hc hd hbc (Ly0.wG_mem Ly0.B0 Ly0.gens0 2 Ly0.gens0_mem _ hz)
    (Fin.ext ((e p0).symm.trans h0)) (Fin.ext ((e p3).symm.trans h3))
    (Fin.ext ((e p1).symm.trans h1))

theorem wG_eq_of_fix {u v : List ℤ} (hu : ∀ l ∈ u, l ≠ 0 ∧ l.natAbs ≤ 2)
    (hv : ∀ l ∈ v, l ≠ 0 ∧ l.natAbs ≤ 2) (h : fixC ((u ++ invW v).map lcode) = true) :
    Ly0.wG Ly0.gens0 u = Ly0.wG Ly0.gens0 v := by
  have hz : ∀ l ∈ u ++ invW v, l ≠ 0 ∧ l.natAbs ≤ 2 := by
    intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · exact hu l hl
    · exact invW_range hv l hl
  have e := wG_eq_one hc hd hbc hz h
  rw [Ly0.wG_append, Ly0.wG_invW Ly0.gens0 fun l hl => (hv l hl).1] at e
  exact mul_inv_eq_one.1 e

end Base

theorem uExp_range {Ut : List ℤ} (hUt : ∀ l ∈ Ut, l ≠ 0 ∧ l.natAbs ≤ 4) :
    ∀ l ∈ uExp Ut, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  obtain ⟨m, hm, hl⟩ := List.mem_flatMap.1 hl
  have hm4 := hUt m hm
  split_ifs at hl with hpos
  · exact Ly0.uWords_mem _ (by omega) l hl
  · exact invW_range (Ly0.uWords_mem _ (by omega)) l hl

theorem wG_uExp {Ut : List ℤ} (hUt : ∀ l ∈ Ut, l ≠ 0 ∧ l.natAbs ≤ 4) :
    Ly0.wG Ly0.gens0 (uExp Ut) = wordG (wordLetter Ly0.uG) Ut := by
  induction Ut with
  | nil => simp [uExp, wordG]
  | cons l Ut ih =>
    have hl := hUt l List.mem_cons_self
    have e : uExp (l :: Ut) = (if 0 < l then Ly0.uWords.getD (l.toNat - 1) []
        else invW (Ly0.uWords.getD ((-l).toNat - 1) [])) ++ uExp Ut := by
      simp [uExp, List.flatMap_cons]
    rw [e, Ly0.wG_append, ih fun l' hl' => hUt l' (List.mem_cons_of_mem _ hl'), wordG_cons']
    congr 1
    by_cases h : 0 < l
    · rw [if_pos h, wordLetter_of_pos _ h, Ly0.uG_def]
    · rw [if_neg h, wordLetter_of_not_pos _ h, Ly0.uG_def,
        Ly0.wG_invW Ly0.gens0 fun m hm => (Ly0.uWords_mem _ (by omega) m hm).1]

theorem txExp_range {t : List (Fin 5 × Bool)} (ht : ∀ l ∈ t, l.1.val < 4) :
    ∀ l ∈ txExp t, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  intro l hl
  obtain ⟨m, hm, hl⟩ := List.mem_flatMap.1 hl
  have hm4 := ht m hm
  split_ifs at hl with hpos
  · exact Glue.txWords_getD_range hm4 l hl
  · exact invW_range (Glue.txWords_getD_range hm4) l hl

theorem wG_txExp {t : List (Fin 5 × Bool)} (ht : ∀ l ∈ t, l.1.val < 4) :
    Ly0.wG Ly0.gens0 (txExp t) = FreeGroup.lift txP (FreeGroup.mk t) := by
  induction t with
  | nil => simp [txExp, ← FreeGroup.one_eq_mk]
  | cons l t ih =>
    have hl := ht l List.mem_cons_self
    have e : txExp (l :: t) = (if l.2 then Glue.txWords.getD l.1.val []
        else invW (Glue.txWords.getD l.1.val [])) ++ txExp t := by
      simp [txExp, List.flatMap_cons]
    have e2 : FreeGroup.mk (l :: t) = FreeGroup.mk [l] * FreeGroup.mk t := rfl
    rw [e, Ly0.wG_append, ih fun l' hl' => ht l' (List.mem_cons_of_mem _ hl'), e2, map_mul,
      lift_mk_single]
    congr 1
    by_cases h : l.2 = true
    · rw [if_pos h, if_pos h, txP_def]
      rfl
    · rw [if_neg h, if_neg h, Ly0.wG_invW Ly0.gens0 fun m hm => (Glue.txWords_getD_range hl m hm).1,
        txP_def]
      rfl

theorem isUWord_iff (w : List ℤ) : isUWord w = true ↔ ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4 := by
  simp [isUWord]

theorem isTxWord_iff (t : List (Fin 5 × Bool)) : isTxWord t = true ↔ ∀ l ∈ t, l.1.val < 4 := by
  simp [isTxWord]

section Holds

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound)
include hc hd hbc

theorem eEvHolds_of_eFix {ev : EEv} (h : eFix ev = true) : EEvHolds ev := by
  obtain ⟨Ut, U, V⟩ := ev
  obtain ⟨hUt, h⟩ := andB_true h
  obtain ⟨hS, h⟩ := andB_true h
  obtain ⟨hU, h⟩ := andB_true h
  obtain ⟨hV, h⟩ := andB_true h
  obtain ⟨h1, h2⟩ := andB_true h
  have hUt' := (isUWord_iff Ut).1 hUt
  have hS' := (isUWord_iff (substW Ut)).1 hS
  refine ⟨hUt', (isBWord_iff U).1 hU, (isBWord_iff V).1 hV, ?_, ?_⟩
  · rw [bCodes_eq, ← List.map_append] at h1
    rw [lift_gB_eq_wG hc hd hU, ← wG_uExp hUt']
    exact wG_eq_of_fix hc hd hbc (wZ_mem _) (uExp_range hUt') h1
  · rw [bCodes_eq, ← List.map_append] at h2
    have hz : ∀ l ∈ uExp (substW Ut) ++ wZ (V.map letIdx), l ≠ 0 ∧ l.natAbs ≤ 2 := by
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact uExp_range hS' l hl
      · exact wZ_mem _ l hl
    have e := wG_eq_one hc hd hbc hz h2
    rw [Ly0.wG_append, wG_uExp hS'] at e
    rw [lift_gB_eq_wG hc hd hV]
    exact e

theorem trSegHolds_of_segFix {sg : TrSeg} (h : segFix sg = true) : TrSegHolds sg := by
  obtain ⟨s, t⟩ := sg
  obtain ⟨hs, h⟩ := andB_true h
  obtain ⟨ht, h⟩ := andB_true h
  have ht' := (isTxWord_iff t).1 ht
  refine ⟨(isBWord_iff s).1 hs, ht', ?_⟩
  rw [bCodes_eq, ← List.map_append] at h
  rw [lift_gB_eq_wG hc hd hs, ← wG_txExp ht']
  exact wG_eq_of_fix hc hd hbc (wZ_mem _) (txExp_range ht') h

end Holds

theorem trCheck_true : Ly243.trCheck = true := by
  simp only [Ly243.trCheck, tablesOK_of, permutesOK_of, fixZeroOK_of, kSwapOK_of, txyKerOK_of,
    txyEnumOK_of, txyCenterOK_of, cosetOK_of, kCompatOK_of, Bool.and_self]

theorem trWordTab_eq : ∀ w : List (Fin 5 × Bool),
    trWordTab w = tabT (unpack 243 8 (wK 243 8 LG (w.map zOf))) ∧ C8 (wK 243 8 LG (w.map zOf))
  | [] => ⟨hid8, base8.2.1⟩
  | l :: w => by
    obtain ⟨ih1, ih2⟩ := trWordTab_eq w
    obtain ⟨g1, g2⟩ := trLetT (zOf_ne_zero l) (by have := l.1.isLt; rw [zOf_natAbs]; omega)
    have e : trWordTab (l :: w) = compT Ly243.deg (Ly243.trLet (zOf l)) (trWordTab w) := rfl
    rw [e, ih1, g1, compT_unpack g2 ih2]
    exact ⟨rfl, canonK_pcomp g2 ih2⟩

theorem lift_gg_eq_one {w : List (Fin 5 × Bool)} (h : Nat.beq (wK 243 8 LG (w.map zOf)) id8 = true) :
    FreeGroup.lift (fun i : Fin 5 => Ly243.gg i.val) (FreeGroup.mk w) = 1 := by
  have hr := rep_trWordTab trCheck_true w
  rw [(trWordTab_eq w).1, Nat.eq_of_beq_eq_true h, ← hid8] at hr
  exact rep_unique hr (Rep.idT (by norm_num))

theorem trEvHolds_of_trFix (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound) {ev : TrEv}
    (h : trFix ev = true) : TrEvHolds ev := by
  obtain ⟨h0, h⟩ := andB_true h
  obtain ⟨hrest, h243⟩ := andB_true h
  exact ⟨trSegHolds_of_segFix hc hd hbc h0,
    fun sg hsg => trSegHolds_of_segFix hc hd hbc (List.all_eq_true.1 hrest sg hsg),
    lift_gg_eq_one h243⟩

theorem eEvCore_holds (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound) :
    ∀ e ∈ eEvCore, EEvHolds e := fun e he =>
  eEvHolds_of_eFix hc hd hbc (List.all_eq_true.1 e_fix e he)

theorem trEvCore_holds (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
    (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound) :
    ∀ ev ∈ trEvCore, TrEvHolds ev := fun ev hev =>
  trEvHolds_of_trFix hc hd hbc (List.all_eq_true.1 tr_fix ev hev)

end CertificateChecks.KernelLyBase

end

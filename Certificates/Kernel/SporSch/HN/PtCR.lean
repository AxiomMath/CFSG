
module

public import Certificates.Kernel.SporSch.HN.PtCK
public import Certificates.Kernel.SporSch.HN.Pt2103
public import Certificates.Kernel.SporSch.HN.CTab
public import Certificates.Kernel.SporSch.HN.Invol2099
public import CFSG.Sporadic.HNOddCore.LCheckInputs
public import CFSG.Sporadic.HNSchreier.InvolSpec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPtC

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.ONSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPt2103 CFSG.Sporadic.He.Native Matrix

local notation "OM" => ordMat 5 133 13 1729

noncomputable abbrev c4J (j : ℕ) : JH := wJ sL InvData.c4Words[j]!

noncomputable abbrev x4J : JH := seedJ InvData.x4Root * wJ sL InvData.x4H

noncomputable abbrev t4J : JH := wJ sL InvData.t4Word

@[expose] noncomputable def genR
    (j : ℕ) : RH :=
  if j < 9 then jR (c4J j) else if j = 9 then jR x4J else cR

@[expose] noncomputable def letR
    (c : ℕ) : RH :=
  if c < 11 then genR c else (genR (c - 11))⁻¹

@[expose] def gcode (l : ℤ) : ℕ := if 0 < l then l.toNat - 1 else 10 + (-l).toNat

@[expose] noncomputable def wordG
    (w : List ℤ) : RH :=
  ((w.map gcode).map letR).prod

theorem letters_c4 : InvData.c4Words.size = 9 ∧
    (∀ j < 9, ∀ l ∈ InvData.c4Words[j]!, l ≠ 0 ∧ l.natAbs ≤ 17) ∧
    (∀ l ∈ InvData.x4H, l ≠ 0 ∧ l.natAbs ≤ 17) ∧ (∀ l ∈ InvData.x4Root, l = 1 ∨ l = 2) ∧
    (∀ l ∈ InvData.t4Word, l ≠ 0 ∧ l.natAbs ≤ 17) := by
  decide +kernel

theorem codes_c4 : (∀ j < 9, CFSG.KD.HNPtC.gcF j = InvData.c4Words[j]!.map scode) ∧
    CFSG.KD.HNPtC.gcF 9 = InvData.x4Root.map (33 + ·) ++ InvData.x4H.map scode ∧
    CFSG.KD.HNPtC.t4c = InvData.t4Word.map scode ∧ (∀ j < 10, ∀ c ∈ CFSG.KD.HNPtC.gcF j, c < 36) ∧
    (∀ c ∈ CFSG.KD.HNPtC.t4c, c < 36) := by
  decide +kernel

theorem GT_canon {c : ℕ} (hc : c < 22) : Canon 5 133 13 (CFSG.KD.HNPtC.GT c) :=
  HNXP.canon_of_validHN (allN_spec valid_GT c hc)

theorem C_mat :
    OM (CFSG.KD.HNPtC.GT 10) = matR cR := by
  have hC : rowsOf 5 133 LocalData.involutionPayload = rows5 (HNInvol.sx 36) := by
    rw [HNInv.eq]
    exact pay5_sound HNInvol.payC
  rw [om_rows bridge_C, ← hC, toMat_rowsC, matR_cR, matCx_eq_matC]

theorem T4_mat :
    Canon 5 133 13 CFSG.KD.HNPtC.T4 ∧ OM CFSG.KD.HNPtC.T4 = matJ t4J := by
  rw [← Nat.eq_of_beq_eq_true w_T4]
  obtain ⟨h1, h2⟩ := mat_word codes_c4.2.2.2.2
  refine ⟨h1, ?_⟩
  rw [h2, codes_c4.2.2.1, prod_scode _ letters_c4.2.2.2.2]

theorem genR_mat {j : ℕ}
    (hj : j < 11) : OM (CFSG.KD.HNPtC.GT j) = matR (genR j) := by
  rcases Nat.lt_or_ge j 10 with h10 | h10
  · rw [← Nat.eq_of_beq_eq_true (allN_spec w_GT j h10), (mat_word (codes_c4.2.2.2.1 j h10)).2,
      genR]
    rcases Nat.lt_or_ge j 9 with h9 | h9
    · rw [if_pos h9, matR_jR, codes_c4.1 j h9, prod_scode _ (letters_c4.2.1 j h9)]
    · obtain rfl : j = 9 := by omega
      rw [if_neg (by omega), if_pos rfl, matR_jR, codes_c4.2.1, List.map_append, List.prod_append,
        prod_seed _ letters_c4.2.2.2.1, prod_scode _ letters_c4.2.2.1]
  · obtain rfl : j = 10 := by omega
    rw [C_mat, genR, if_neg (by omega), if_neg (by omega)]

theorem letR_mat {c : ℕ}
    (hc : c < 22) : OM (CFSG.KD.HNPtC.GT c) = matR (letR c) := by
  rw [letR]
  rcases Nat.lt_or_ge c 11 with h | h
  · rw [if_pos h, genR_mat h]
  · rw [if_neg (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, c = 11 + j := ⟨c - 11, by omega⟩
    have e0 : CFSG.KC.LL.HN.mm (CFSG.KD.HNPtC.GT j) (CFSG.KD.HNPtC.GT (11 + j)) =
        CFSG.KD.OrdHN.ONE := Nat.eq_of_beq_eq_true (allN_spec inv_GT j (by omega))
    have e := congrArg OM e0
    rw [(HNXP.mm_sound (GT_canon (by omega)) (GT_canon hc)).2, HNXP.one_ord,
      genR_mat (by omega)] at e
    rw [Nat.add_sub_cancel_left]
    calc OM (CFSG.KD.HNPtC.GT (11 + j))
        = matR (genR j)⁻¹ * (matR (genR j) * OM (CFSG.KD.HNPtC.GT (11 + j))) := by
          rw [← Matrix.mul_assoc, ← matR_mul, inv_mul_cancel, matR_one, Matrix.one_mul]
      _ = matR (genR j)⁻¹ := by rw [e, Matrix.mul_one]

theorem wordGT_mat :
    ∀ cs : List ℕ, (∀ c ∈ cs, c < 22) →
    Canon 5 133 13 (wordC CFSG.KD.HNPtC.GT cs) ∧
      OM (wordC CFSG.KD.HNPtC.GT cs) = matR (cs.map letR).prod := by
  intro cs hcs
  obtain ⟨h1, h2⟩ := HNXP.wordC_sound cs fun c hc => GT_canon (hcs c hc)
  refine ⟨h1, h2.trans ?_⟩
  clear h1 h2
  induction cs with
  | nil => rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, matR_one]
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, matR_mul,
      letR_mat (hcs c List.mem_cons_self), ih fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')]

theorem ri_pts {r : RH} {W : ℕ}
    (hW : Canon 5 133 13 W) (hm : OM W = matR r) {FL IL c : ℕ} (hc : c ≤ 64)
    (h : ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M (trM W) FL IL c =
      true)
    {k : ℕ} (hk : k < c) (h1 : fldW FL (21 * k) 21 < nPts) (h2 : fldW IL (21 * k) 21 < nPts) :
    ((r • (⟨fldW FL (21 * k) 21, h1⟩ : X) : X) : ℕ) = fldW IL (21 * k) 21 := by
  have e : vL (r • (⟨fldW FL (21 * k) 21, h1⟩ : X) : X) = vL (⟨fldW IL (21 * k) 21, h2⟩ : X) := by
    rw [vL_smul]
    change matR r *ᵥ vL (fldW FL (21 * k) 21) = vL (fldW IL (21 * k) 21)
    rw [vL_eq h1, vL_eq h2, PK_eq h1, PK_eq h2, ← hm,
      HNXP.ptsImg_sound consts_parts.1 consts_parts.2 hW hc h k hk]
  exact congrArg Fin.val (vL_injective e)

theorem hStrongArr_SJ : hStrongArr = SJ := by
  rw [hStrongArr_eq, hRegs_eq, hns_n, natTab_alpha, natTab_beta, regs_get (k := 1) (by omega),
    regs_get (k := 2) (by omega), hS_eq]

theorem pword_SJ {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 17) :
    pword nPts SJ (pinvs nPts SJ) w = arrJ (wJ sL w) :=
  pword_arrJ SJ_arrs _ hw

theorem seedWordArr_arrJ :
    ∀ w : List ℕ, seedWordArr nPts (arrJ aJ) (arrJ bJ) w = arrJ (seedJ w)
  | [] => pid_arrJ
  | l :: w => by
    rw [seedWordArr, seedWordArr_arrJ w, seedJ]
    split_ifs <;> exact pcomp_arrJ _ _

theorem prep_arrJ (g : JH) :
    PRep hnsData.n (arrJ g) (permR (jR g)) := fun x => by
  rw [arrJ_get g x.isLt, gi_of_lt g x.isLt, permR_jR, permJ_apply]

noncomputable abbrev gTabsJ : Array (Array ℕ) := genTabs nPts (arrJ aJ) (arrJ bJ) SJ cRec

theorem gTabsA_size :
    ((InvData.c4Words.extract 0 9).map (pword nPts SJ (pinvs nPts SJ))).size = 9 := by
  simp [letters_c4.1]

theorem gTabsJ_size : gTabsJ.size = 11 := by
  simp [gTabsJ, genTabs, letters_c4.1]

theorem gTabsJ_get {j : ℕ} (hj : j < 9) :
    gTabsJ[j]! = pword nPts SJ (pinvs nPts SJ) InvData.c4Words[j]! := by
  unfold gTabsJ genTabs
  rw [getElem!_pos _ j (by simp [letters_c4.1]; omega),
    Array.getElem_push_lt (by simp [letters_c4.1]; omega),
    Array.getElem_push_lt (by simp [letters_c4.1]; omega), Array.getElem_map,
    Array.getElem_extract, ← getElem!_pos InvData.c4Words (0 + j) (by rw [letters_c4.1]; omega)]
  simp

theorem gTabsJ_nine : gTabsJ[9]! = pcomp nPts (seedWordArr nPts (arrJ aJ) (arrJ bJ)
    InvData.x4Root) (pword nPts SJ (pinvs nPts SJ) InvData.x4H) := by
  unfold gTabsJ genTabs
  rw [getElem!_pos _ 9 (by simp [letters_c4.1]), Array.getElem_push_lt (by simp [letters_c4.1]),
    Array.getElem_push, dite_eq_right (by rw [gTabsA_size]; omega)]

theorem gTabsJ_ten : gTabsJ[10]! = cRec := by
  unfold gTabsJ genTabs
  rw [getElem!_pos _ 10 (by simp [letters_c4.1]), Array.getElem_push,
    dite_eq_right (by simp [letters_c4.1])]

theorem prep_genTabs
    {j : ℕ} (hj : j < 11) :
    PRep hnsData.n gTabsJ[j]! (permR (genR j)) := by
  rw [genR]
  rcases Nat.lt_or_ge j 9 with h9 | h9
  · rw [if_pos h9, gTabsJ_get h9, pword_SJ (letters_c4.2.1 j h9)]
    exact prep_arrJ _
  rcases Nat.lt_or_ge j 10 with h10 | h10
  · obtain rfl : j = 9 := by omega
    rw [if_neg (by omega), if_pos rfl, gTabsJ_nine, seedWordArr_arrJ, pword_SJ letters_c4.2.2.1,
      pcomp_arrJ]
    exact prep_arrJ _
  · obtain rfl : j = 10 := by omega
    rw [if_neg (by omega), if_neg (by omega), gTabsJ_ten]
    exact HNCTab.prep_cRec'

theorem prep_genTabs_inv
    {j : ℕ} (hj : j < 11) :
    PRep hnsData.n (pinvs nPts gTabsJ)[j]! (permR (genR j))⁻¹ ∧
      pisInv nPts gTabsJ[j]! (pinvs nPts gTabsJ)[j]! = true := by
  rw [pinvs_get (by rw [gTabsJ_size]; exact hj)]
  exact BfsPar.prep_pinvCand (prep_genTabs hj)

theorem letR_gcode {l : ℤ}
    (hl : l ≠ 0 ∧ l.natAbs ≤ 11) :
    letR (gcode l) = if 0 < l then genR (l.toNat - 1) else (genR ((-l).toNat - 1))⁻¹ := by
  unfold letR gcode
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp, if_pos (by omega)]
  · rw [if_neg hp, if_neg hp, if_neg (by omega), show 10 + (-l).toNat - 11 = (-l).toNat - 1 by
      omega]

theorem evalWordPt_eq
    {T Ti : Array (Array ℕ)} (hT : ∀ j < 11, PRep hnsData.n T[j]! (permR (genR j)))
    (hTi : ∀ j < 11, PRep hnsData.n Ti[j]! (permR (genR j))⁻¹) :
    ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 11) → ∀ x : X,
      evalWordPt T Ti w x = ((wordG w • x : X) : ℕ)
  | [], _, x => by
    rw [evalWordPt, wordG, List.map_nil, List.map_nil, List.prod_nil, one_smul]
  | l :: w, hw, x => by
    have hl := hw l List.mem_cons_self
    have ih := evalWordPt_eq hT hTi w (fun z hz => hw z (List.mem_cons_of_mem l hz)) x
    have e : wordG (l :: w) = letR (gcode l) * wordG w := by
      rw [wordG, wordG, List.map_cons, List.map_cons, List.prod_cons]
    change (if 0 < l then (T[l.toNat - 1]!)[evalWordPt T Ti w x]!
      else (Ti[(-l).toNat - 1]!)[evalWordPt T Ti w x]!) = _
    rw [ih, e, mul_smul, letR_gcode hl]
    by_cases hp : 0 < l
    · rw [if_pos hp, if_pos hp]
      exact (hT _ (by omega) _).trans (by rw [permR_apply])
    · rw [if_neg hp, if_neg hp]
      exact (hTi _ (by omega) _).trans (by rw [← map_inv, permR_apply])

end CertificateChecks.KernelSporSch.HNPtC

end

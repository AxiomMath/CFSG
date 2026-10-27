module

public import Certificates.Kernel.Th.DModel.Chk
public import Certificates.Kernel.Th.DModel.Mat
public import Certificates.Kernel.Th.AutD.Final
public import CFSG.Certificates.Kernel.Th.Spec.Rows
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Th.Checks2.Surj_K
import CFSG.Certificates.Kernel.Spor.EnumBaseSound
import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.Th.Spec.Gj
public import CFSG.Certificates.Kernel.Th.Spec.SurjCheckBase

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.DModel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KS.PEnum CertificateChecks.KernelTh CertificateChecks.KernelTh.AutD
open CFSG.Sporadic.Th.Recog CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

section Mat

open CFSG.KC.Th CFSG.KC.Th.Spec CFSG.KC.Th.SurjS CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Th.Max3

theorem hrm : CFSG.KD.ThS.rm = 2 ^ 248 - 1 := (consts_spec CFSG.KD.ThS.k0).2.1

theorem img : CFSG.Sporadic.Bridge.Th.imgMats.size = 8 ∧ ∀ g < 8,
    WfRows (CFSG.Sporadic.Bridge.Th.imgMats[g]?.getD (Native.idRows ())) ∧
      rowsMatrix (CFSG.Sporadic.Bridge.Th.imgMats[g]?.getD (Native.idRows ())) =
        pkMat (CFSG.KD.ThSj.RB (g + 1)) :=
  imgMats_spec hrm CFSG.KD.ThSj.LI_eq CFSG.KC.Th.SurjK.text

theorem rowsG_spec (i : Fin 8) :
    WfRows (rowsG i) ∧ rowsMatrix (rowsG i) = regMat CFSG.KD.ThSj.RB (i.val, true) :=
  img.2 i.val i.isLt

theorem rowsGInv_spec (i : Fin 8) :
    WfRows (rowsGInv i) ∧ rowsMatrix (rowsGInv i) = regMat CFSG.KD.ThSj.RB (i.val, false) := by
  have hX := img.2 i.val i.isLt
  have hi : i.val < CFSG.Sporadic.Bridge.Th.imgMats.size := by rw [img.1]; exact i.isLt
  have hinv : rowsMatrix (CFSG.Sporadic.Bridge.Th.imgMats[i.val]?.getD (Native.idRows ())) *
      pkMat (CFSG.KD.ThSj.RB (i.val + 9)) = 1 := by
    rw [hX.2, ← pkMat_mulB CFSG.KD.ThS.k0, regsOK_mul CFSG.KC.Th.SurjK.regs i.val i.isLt,
      pkMat_one CFSG.KD.ThS.k0]
  have e : rowsGInv i =
      invRows (CFSG.Sporadic.Bridge.Th.imgMats[i.val]?.getD (Native.idRows ())) := by
    unfold rowsGInv
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hi, Option.map_some, Option.getD_some,
      Option.getD_some]
  obtain ⟨hs, hw, -, -⟩ := invRows_spec _ hX.1.1 hX.1.2 ⟨_, hinv⟩
  rw [e]
  exact ⟨⟨hs, hw⟩, rowsMatrix_invRows_eq _ hX.1.1 hX.1.2 hinv⟩

theorem wRows_spec (w : List (Fin 8 × Bool)) : WfRows (wRows rowsG rowsGInv w) ∧
    rowsMatrix (wRows rowsG rowsGInv w) =
      (w.map fun l => regMat CFSG.KD.ThSj.RB (l.1.val, l.2)).prod := by
  unfold wRows
  refine ⟨wfRows_prodRows ?_, ?_⟩
  · intro X hX
    obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hX
    cases b
    · exact (rowsGInv_spec g).1
    · exact (rowsG_spec g).1
  · rw [Spec.rowsMatrix_prodRows, List.map_map]
    congr 1
    apply List.map_congr_left
    rintro ⟨g, b⟩ -
    cases b
    · exact (rowsGInv_spec g).2
    · exact (rowsG_spec g).2

theorem codeW_lett (w : List (Fin 8 × Bool)) :
    (codeW w).map lettOfCode = w.map fun l => (l.1.val, l.2) := by
  unfold codeW
  rw [List.map_map]
  apply List.map_congr_left
  rintro ⟨g, b⟩ -
  cases b
  · refine Prod.ext ?_ ?_
    · change (2 * g.val + 1) / 2 = g.val
      omega
    · change decide ((2 * g.val + 1) % 2 = 0) = false
      exact decide_eq_false (by omega)
  · refine Prod.ext ?_ ?_
    · change (2 * g.val + 0) / 2 = g.val
      omega
    · change decide ((2 * g.val + 0) % 2 = 0) = true
      exact decide_eq_true (by omega)

theorem codeW_lt (w : List (Fin 8 × Bool)) : ∀ x ∈ codeW w, x / 2 < 8 := by
  intro x hx
  unfold codeW at hx
  obtain ⟨⟨g, b⟩, -, rfl⟩ := List.mem_map.1 hx
  have hg := g.isLt
  cases b
  · change (2 * g.val + 1) / 2 < 8
    omega
  · change (2 * g.val + 0) / 2 < 8
    omega

theorem wordMatFrom_eq (M : Matrix (Fin 248) (Fin 248) (ZMod 2)) (w : List (ℕ × Bool)) :
    wordMatFrom CFSG.KD.ThSj.RB M w = M * (w.map (regMat CFSG.KD.ThSj.RB)).prod := by
  induction w generalizing M with
  | nil => simp [wordMatFrom]
  | cons l w ih =>
    unfold wordMatFrom at ih ⊢
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem duQ_eq : pkMat duQ = rowsMatrix (rowsHsw 3) * rowsMatrix (rowsHsw 7) := by
  have h := wordV_spec (RB := CFSG.KD.ThSj.RB) CFSG.KD.ThS.k0 (codeW (hswWord 3 ++ hswWord 7))
    CFSG.KD.ThS.ONE (codeW_lt _)
  unfold duQ
  rw [h, pkMat_one CFSG.KD.ThS.k0, wordMatFrom_eq, one_mul, codeW_lett, List.map_map,
    List.map_append, List.prod_append]
  unfold rowsHsw
  rw [(wRows_spec _).2, (wRows_spec _).2]
  rfl

theorem du_ok : eqRows (prodRows (List.replicate 6 (mulRows (rowsHsw 3) (rowsHsw 7)))) idRows =
    true := by
  have hw : WfRows (mulRows (rowsHsw 3) (rowsHsw 7)) :=
    wfRows_mulRows (wRows_spec _).1 (wRows_spec _).1
  refine eqRows_of_rowsMatrix_eq (wfRows_prodRows fun X hX => ?_) wfRows_idRows ?_
  · rw [List.eq_of_mem_replicate hX]
    exact hw
  · rw [Spec.rowsMatrix_prodRows, rowsMatrix_idRows, List.map_replicate, List.prod_replicate,
      rowsMatrix_mulRows, ← duQ_eq]
    have e := congrArg pkMat (Nat.eq_of_beq_eq_true k_du)
    rw [pkMat_mulB CFSG.KD.ThS.k0, pkMat_mulB CFSG.KD.ThS.k0, pkMat_mulB CFSG.KD.ThS.k0,
      pkMat_mulB CFSG.KD.ThS.k0, pkMat_mulB CFSG.KD.ThS.k0, pkMat_one CFSG.KD.ThS.k0] at e
    rw [← e]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]

end Mat

theorem let_inv {j : Nat} (hj : j < 6) : pc (LI j) (L j) = pidn 51 6 := by
  obtain ⟨-, -, e⟩ := (by simpa only [andB_eq, Bool.and_eq_true] using
    CFSG.KS.Raw.Orb.allN_iff.1 k_let j hj :
    canonK 51 6 (mask 6) (51 * 6) (LI j) = true ∧ Nat.beq (pc (L j) (LI j)) (pidn 51 6) = true ∧
      Nat.beq (pc (LI j) (L j)) (pidn 51 6) = true)
  exact Nat.eq_of_beq_eq_true e

theorem pis_ok : ∀ j : Fin 6,
    CFSG.ONSchreier.Native.pisInv 51 letArr[j.val]! (letInv ())[j.val]! = true := by
  intro j
  obtain ⟨a, b, c, d⟩ := let_get j.isLt
  rw [a, c]
  exact pisInv_unpack b d (let_inv j.isLt)

theorem RD_eq : RD = rdC ++ [duSix] := by
  unfold RD rdHSW rdC
  rw [R0'_eq]

theorem rd_ok : rdCheck () = true := by
  unfold rdCheck
  dsimp only
  have h := k_rd
  rw [allL_iff, List.all_eq_true] at h
  rw [RD_eq, List.all_eq_true]
  intro w hw
  obtain ⟨a, b⟩ := wL w
  rw [a, idT, beqU b cE]
  exact h w hw

theorem tc_ok : tConjCheck () = true := by
  unfold tConjCheck
  dsimp only
  rw [List.all_eq_true]
  intro j _
  obtain ⟨a, b, c, d⟩ := let_get j.isLt
  obtain ⟨a5, b5, c5, d5⟩ := let_get (j := 5) (by decide)
  have h := CFSG.KS.Raw.Orb.allN_iff.1 k_tc j.val j.isLt
  by_cases h4 : j.val = 4
  · have e4 : (j.val == 4) = true := by simp [h4]
    have e4' : Nat.beq j.val 4 = true := by rw [h4]; rfl
    rw [if_pos e4, a, a5, c, c5, compU b b5, compU (cpc b b5) d, beqU (cpc (cpc b b5) d) d5]
    rw [e4'] at h
    exact h
  · have e4 : ¬ (j.val == 4) = true := by simpa using h4
    have e4' : Nat.beq j.val 4 = false := by
      cases hb : Nat.beq j.val 4
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h4
    rw [if_neg e4, a, a5, c, compU b b5, compU (cpc b b5) d, beqU (cpc (cpc b b5) d) b5]
    rw [e4'] at h
    exact h

theorem enum_ok : enumOK 51 letArr (dEnum ()) = true := by
  rw [dEnum_eq.1]
  exact dEnum_eq.2

theorem ofFn_val {α : Type} (n : Nat) (f : Nat → α) :
    List.ofFn (n := n) (fun i => f i.val) = (List.range n).map f :=
  List.ext_getElem (by simp) fun i _ _ => by simp

theorem sq_ok : (sqTabs ()).length = 164 := by
  unfold sqTabs
  rw [dEnum_eq.1, penumRec_eq]
  dsimp only
  rw [Array.toList_ofFn, ofFn_val ADE.cnt (fun i => unpack 51 6 (ADE.T i)), List.filter_map,
    List.length_map, ← List.countP_eq_length_filter, enum_parts.2.1]
  have h := Nat.eq_of_beq_eq_true k_sq
  rw [CFSG.KS.EnumBase.cntN_eq] at h
  rw [← h]
  apply List.countP_congr
  intro i hi
  have hi' : i < 3456 := List.mem_range.1 hi
  rw [Function.comp_apply, compU (cT hi') (cT hi'), idT, beqU (cpc (cT hi') (cT hi')) cE]
  rfl

theorem orb_parts {r : Nat} (hr : r < 12) : ok r = 6 ∧ oc r ≤ 144 ∧
    (∀ j < 6, oG r j = L j ∧ oGI r j = LI j) ∧
    penumHdK (oX r) (oc r) 3456 (oT r) (oPL r) = true ∧
    penumSlK 51 6 (mask 6) (51 * 6) true (oG r) (oGI r) (ok r) (oc r) (oT r) (oPL r) (oPOS r)
      (oSRT r) (oSRI r) 0 144 = true := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 k_orb r hr
  obtain ⟨h1, h⟩ := andT h
  obtain ⟨h2, h⟩ := andT h
  obtain ⟨h3, h⟩ := andT h
  obtain ⟨h4, h5⟩ := andT h
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.le_of_ble_eq_true h2, fun j hj => ?_, h4, h5⟩
  obtain ⟨e1, e2⟩ := andT (CFSG.KS.Raw.Orb.allN_iff.1 h3 j hj)
  exact ⟨Nat.eq_of_beq_eq_true e1, Nat.eq_of_beq_eq_true e2⟩

theorem orb_pt {r : Nat} (hr : r < 12) : ∀ i < oc r, penumPtK 51 6 (mask 6) (51 * 6) true
    (oG r) (oGI r) (ok r) (oc r) (oT r) (oPL r) (oPOS r) (oSRT r) (oSRI r) i = true := by
  intro i hi
  have := (orb_parts hr).2.1
  exact penumSl_spec (orb_parts hr).2.2.2.2 i (Nat.zero_le _) (by omega) hi

theorem primeOrbs_size : (primeOrbs ()).size = 12 := by
  unfold primeOrbs
  simp [primeReps]

theorem primeOrbs_get {r : Nat} (hr : r < 12) : (primeOrbs ())[r]! =
    orbitBFS 51 letArr (letInv ()) (wTab letArr (letInv ()) (primeReps.getD r [])) 3456 := by
  have hl : primeReps.length = 12 := rfl
  rw [getElem!_pos _ r (by rw [primeOrbs_size]; exact hr)]
  unfold primeOrbs
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hr)]

theorem orb_enc {r : Nat} (hr : r < 12) :
    (primeOrbs ())[r]! = penumRec 51 6 (oc r) (oT r) (oPL r) ∧
    treeOK (conjStep 51 letArr (letInv ())) letArr.size
      (wTab letArr (letInv ()) (primeReps.getD r [])) (penumRec 51 6 (oc r) (oT r) (oPL r)) =
        true := by
  obtain ⟨hk, -, hG, hh, -⟩ := orb_parts hr
  have hg : GensOK 51 6 (ok r) (oG r) letArr := by
    rw [hk]; exact gensO fun j hj => (hG j hj).1
  have hgi : GensOK 51 6 (ok r) (oGI r) (letInv ()) := by
    rw [hk]; exact gensOI fun j hj => (hG j hj).2
  rw [primeOrbs_get hr]
  exact penumK_conj_sound sz hg hgi (wL _).1 hh (orb_pt hr)

theorem tgt_eq (i : Nat) : targetTab (letInv ()) i = unpack 51 6 (tgtK i) ∧ Cn (tgtK i) := by
  obtain ⟨a0, b0, -, -⟩ := let_get (j := 0) (by decide)
  obtain ⟨a5, b5, c5, d5⟩ := let_get (j := 5) (by decide)
  unfold targetTab tgtK
  by_cases h0 : i = 0
  · subst h0
    exact ⟨a0, b0⟩
  · have e0 : Nat.beq i 0 = false := by
      cases hb : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h0
    rw [if_neg (by simpa using h0), e0]
    by_cases h1 : i = 1
    · subst h1
      exact ⟨a5, b5⟩
    · have e1 : Nat.beq i 1 = false := by
        cases hb : Nat.beq i 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) h1
      rw [if_neg (by simpa using h1), e1]
      exact ⟨c5, d5⟩

theorem kerProd_eq {X : Nat} (hX : Cn X) : ∀ Ls : List (List (Fin 6 × Bool) × Nat),
    kerProd (letInv ()) (unpack 51 6 X) Ls = unpack 51 6 (kerK X Ls) ∧ Cn (kerK X Ls)
  | [] => ⟨idT, cE⟩
  | ck :: Ls => by
    obtain ⟨ih1, ih2⟩ := kerProd_eq hX Ls
    have e1 : kerProd (letInv ()) (unpack 51 6 X) (ck :: Ls) =
        comp 51 (comp 51 (comp 51 (wTab letArr (letInv ()) ck.1)
          (if ck.2 == 2 then comp 51 (unpack 51 6 X) (unpack 51 6 X) else unpack 51 6 X))
          (wTab letArr (letInv ()) (FreeGroup.invRev ck.1)))
          (kerProd (letInv ()) (unpack 51 6 X) Ls) := rfl
    have e2 : kerK X (ck :: Ls) = pc (pc (pc (wK L LI ck.1)
        (Bool.rec (motive := fun _ => Nat) X (pc X X) (Nat.beq ck.2 2)))
        (wK L LI (FreeGroup.invRev ck.1))) (kerK X Ls) := rfl
    have hk : (if ck.2 == 2 then comp 51 (unpack 51 6 X) (unpack 51 6 X) else unpack 51 6 X) =
        unpack 51 6 (Bool.rec (motive := fun _ => Nat) X (pc X X) (Nat.beq ck.2 2)) ∧
        Cn (Bool.rec (motive := fun _ => Nat) X (pc X X) (Nat.beq ck.2 2)) := by
      by_cases h2 : ck.2 = 2
      · have e : Nat.beq ck.2 2 = true := by rw [h2]; rfl
        rw [if_pos (by simp [h2]), e]
        exact ⟨compU hX hX, cpc hX hX⟩
      · have e : Nat.beq ck.2 2 = false := by
          cases hb : Nat.beq ck.2 2
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hb) h2
        rw [if_neg (by simpa using h2), e]
        exact ⟨rfl, hX⟩
    obtain ⟨w1, w2⟩ := wL ck.1
    obtain ⟨v1, v2⟩ := wL (FreeGroup.invRev ck.1)
    rw [e1, e2, w1, v1, hk.1, ih1, compU w2 hk.2, compU (cpc w2 hk.2) v2,
      compU (cpc (cpc w2 hk.2) v2) ih2]
    exact ⟨rfl, cpc (cpc (cpc w2 hk.2) v2) ih2⟩

theorem cov_get {i : Nat} (hi : i < 3456) : ptD i = true := by
  have hs : i / 384 < 9 := by omega
  have h := CFSG.KS.Raw.Orb.allN_iff.1 (by
    have h1 := cAll (i / 384) hs
    unfold cSl at h1
    exact h1) (i % 384) (Nat.mod_lt _ (by decide))
  rw [strictB_app] at h
  have e : Nat.add (Nat.mul 384 (i / 384)) (i % 384) = i := Nat.div_add_mod i 384
  rwa [e] at h

theorem ker_ok : kerCheck () = true := by
  unfold kerCheck
  dsimp only
  rw [Bool.and_eq_true, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.BfsReplay.allBelow_iff, E_size]
  constructor
  · intro r hr
    obtain ⟨e1, e2⟩ := orb_enc hr
    rw [e1]
    unfold orbitOK
    rw [invs_let, e2, Bool.true_and, Bool.true_and]
    unfold kerWitOK
    have hX : Cn (oX r) := (wL _).2
    rw [(wL (primeReps.getD r [])).1]
    obtain ⟨k1, k2⟩ := kerProd_eq hX (primeWit.getD r ([], 0)).1
    obtain ⟨t1, t2⟩ := tgt_eq (primeWit.getD r ([], 0)).2
    change (kerProd (letInv ()) (unpack 51 6 (oX r)) (primeWit.getD r ([], 0)).1 ==
      targetTab (letInv ()) (primeWit.getD r ([], 0)).2) = true
    rw [k1, t1, beqU k2 t2]
    exact CFSG.KS.Raw.Orb.allN_iff.1 k_wit r hr
  · intro i hi
    have c := cT hi
    have h := cov_get hi
    unfold ptD at h
    rw [strictB_app, strictB_app] at h
    rw [E_get hi, idT, compU c c, compU c (cpc c c), beqU c cE, beqU (cpc c c) cE,
      beqU (cpc c (cpc c c)) cE]
    simp only [orB_eq, andB_eq, notB_eq] at h
    rw [Bool.or_eq_true, Bool.or_eq_true] at h ⊢
    rcases h with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · right
      unfold inO at h
      rw [notAllNotB] at h
      obtain ⟨r, hr, h⟩ := h
      unfold inR at h
      rw [notAllNotB] at h
      obtain ⟨q, hq, e⟩ := h
      rw [CFSG.KC.L34KSnd.anyBelow_iff]
      refine ⟨r, hr, ?_⟩
      rw [CFSG.KC.L34KSnd.map_get _ (by rw [primeOrbs_size]; exact hr), (orb_enc hr).1,
        found_penumRec_iff (orb_pt hr) c]
      exact ⟨q, hq, Nat.eq_of_beq_eq_true e⟩

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
theorem dModel_true :
    eqRows (prodRows (List.replicate 6 (mulRows (rowsHsw 3) (rowsHsw 7)))) idRows = true ∧
      (∀ j : Fin 6,
        CFSG.ONSchreier.Native.pisInv 51 letArr[j.val]! (letInv ())[j.val]! = true) ∧
      invsOK 51 letArr (letInv ()) = true ∧
      rdCheck () = true ∧
      tConjCheck () = true ∧
      enumOK 51 letArr (dEnum ()) = true ∧
      (dEnum ()).tabs.size = 3456 ∧
      kerCheck () = true ∧
      (sqTabs ()).length = 164 :=
  ⟨du_ok, pis_ok, invs_let, rd_ok, tc_ok, enum_ok, E_size, ker_ok, sq_ok⟩

end CertificateChecks.KernelTh.DModel

end

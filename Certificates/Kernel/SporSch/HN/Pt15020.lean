module

public import Certificates.Kernel.SporSch.HN.Pt2086
public import Certificates.Kernel.SporSch.HN.Pt15020K
public import Certificates.Kernel.Sporadic.OddCore.HNT4K
public import Certificates.Kernel.Sporadic.OddCore.HN2088
public import Certificates.Kernel.Sporadic.OddCore.HN2089
public import CFSG.Certificates.Kernel.Spor.HNT4Sound
public import CFSG.Certificates.Kernel.Spor.HNAOrbSound
public import CFSG.Certificates.Kernel.Spor.EnumBaseSound
public import CFSG.Certificates.Kernel.LocalQTNatsXSound
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNTests
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPt15020

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr
open CFSG.KS.Ord CFSG.KS.Raw CFSG.KS.HNT4 CFSG.KS.EnumBase CFSG.KC.LQT.NP
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.ONSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CFSG.ComponentClassification.RankTwoSporadic.HN
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPtC CertificateChecks.KernelSpor Matrix

local notation "OM" => ordMat 5 133 13 1729

theorem parse_eq {s : String} {cs : List Char} {L : List Nat} (hs : s = String.ofList cs)
    (h : natsOK cs L = true) : parseNatsHN s = L.toArray := by
  unfold parseNatsHN
  rw [hs]
  exact congrArg List.toArray (natsX_sound cs L h)

theorem pool_eq : decodePoolT4 hnT4PoolStr =
    Array.ofFn (n := 64) fun j => poolRec HNT4T.QN HNT4T.QP j.val :=
  decodePoolT4_sound (by rw [parse_eq HNT4T.Pool.eq HNT4S.pPool, HNA.listUp_eq]) HNT4S.posQ

theorem wits_eq : decodeT4 hnT4WitStr =
    Array.ofFn (n := 16384) fun j => t4Wit HNT4T.WN HNT4T.WP j.val :=
  decodeT4_sound (by rw [parse_eq HNT4T.Wit.eq HNT4S.pWit, HNA.listUp_eq]) HNT4S.posW

theorem pool_get {f : Nat} (hf : f < 64) :
    (decodePoolT4 hnT4PoolStr)[f]! = poolRec HNT4T.QN HNT4T.QP f := by
  rw [pool_eq, getElem!_pos _ f (by simpa using hf), Array.getElem_ofFn]

theorem pool_size : (decodePoolT4 hnT4PoolStr).size = 64 := by
  rw [pool_eq, Array.size_ofFn]

theorem wits_get {k : Nat} (hk : k < 16384) :
    (decodeT4 hnT4WitStr)[k]! = t4Wit HNT4T.WN HNT4T.WP k := by
  rw [wits_eq, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem letsK_spec {WN : Nat → Nat} {s L : Nat} (h : letsK WN s L = true) :
    ∀ x ∈ HNA.listUp (fun t => WN (Nat.add s t)) L, 11 < x ∧ x < 22 := by
  intro x hx
  have := (allL_iff' _ _).1 h x hx
  rw [bAnd_eq', Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at this
  exact this

theorem sub11 (x : Nat) : Int.subNatNat x (nat_lit 11) = (x : Int) - 11 := by
  rw [Int.subNatNat_eq_coe]
  rfl

theorem wordAt_lets {WN : Nat → Nat} {s L : Nat} (h : letsK WN s L = true) :
    ∀ l ∈ wordAt WN s L, 1 ≤ l ∧ l ≤ 10 := by
  intro l hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  obtain ⟨h1, h2⟩ := letsK_spec h x hx
  rw [sub11]
  omega

theorem pool_lets {f : Nat} (hf : f < 64) :
    (∀ l ∈ (poolRec HNT4T.QN HNT4T.QP f).1, 1 ≤ l ∧ l ≤ 10) ∧
      ∀ l ∈ (poolRec HNT4T.QN HNT4T.QP f).2, 1 ≤ l ∧ l ≤ 10 := by
  have h := allN_spec HNT4S.letQ f hf
  unfold poolLetK at h
  rw [strictB_eq', bAnd_eq', Bool.and_eq_true] at h
  exact ⟨wordAt_lets h.1, wordAt_lets h.2⟩

theorem plettersOK_of {w : List Int} (h : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 10) : plettersOK 10 w = true := by
  simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
  intro l hl
  obtain ⟨h1, h2⟩ := h l hl
  omega

theorem cm_facts {f : Nat} (hf : f < 64) :
    (poolT4 (decodePoolT4 hnT4PoolStr))[f]! =
      (unpack 800 10 (HNT4C.P f), unpack 800 10 (HNT4C.Q f)) ∧ Cn (HNT4C.P f) ∧ Cn (HNT4C.Q f) := by
  have h := sliceK_spec (S := 16) (by norm_num) (by norm_num) (fun s hs => HNT4S.cmK.all s hs) f hf
  unfold HNT4S.cmF at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have pS' : allN 11 (fun j => permOK 800 10 (mask 10) (800 * 10) (HQS j) (HNT4S.qi j)) = true :=
    HN2089.pS
  have w1 := (Prim.wordEqK_sound HN2089.s_get pS' h1).1
  have w2 := (Prim.wordEqK_sound HN2089.s_get pS' h2).1
  refine ⟨?_, (CFSG.KC.BfsPin.PP_of_permOK sz800 h3).1, (CFSG.KC.BfsPin.PP_of_permOK sz800 h4).1⟩
  unfold poolT4
  rw [getElem!_pos _ f (by rw [Array.size_map, pool_size]; exact hf), Array.getElem_map,
    ← getElem!_pos _ f (by rw [pool_size]; exact hf), pool_get hf]
  unfold rho4W
  rw [HN2089.pword_eq_wordA, HN2089.pword_eq_wordA, HN2089.pinvs_eq_rawInvs]
  exact Prod.ext w1 w2

theorem pE_get {k : Nat} (hk : k < 16384) : pE[k]! = unpack 800 10 (HPE.T k) := by
  change (pEnum InvData.pgenPerms InvData.parRecs)[k]! = _
  rw [HN2088.pEnum_eq, HN2088.EA_get hk]

theorem wt_ok {k : Nat} (hk : k < 16384) :
    t4WK HNT4S.bp HNT4T.WN HNT4T.WP HPE.T HNT4C.P HNT4C.Q (pidn 800 10) 64 k = true := by
  refine sliceK_spec (L := 64) (S := 256) (by norm_num) (by norm_num) (fun s hs => ?_) k hk
  have := HNT4S.wtK.all s hs
  unfold HNT4S.wt at this
  rwa [strictB_eq'] at this

theorem par_facts {r : Nat} (hr : r < 16384) (h0 : r ≠ 0) :
    pparOf InvData.parRecs r < r ∧ plabOf InvData.parRecs r < 14 ∧
      pparOf InvData.parRecs r = CFSG.KS.PEnum.parOf HPE.PL r ∧
      plabOf InvData.parRecs r = CFSG.KS.PEnum.labOf HPE.PL r := by
  obtain ⟨e1, e2⟩ := HN2088.par_get r hr
  obtain ⟨h1, h2, -⟩ := (recK_spec (HN2088.rec_get r hr)).2 h0
  rw [e1, e2]
  exact ⟨h1, h2, rfl, rfl⟩

theorem lift_fuel (T Ti : Array (Array Nat)) (x : Nat) : ∀ r < 16384, ∀ f, r ≤ f →
    evalLiftF T Ti InvData.parRecs f r x = evalLift T Ti InvData.parRecs r x := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro hr f hf
    rcases Nat.eq_zero_or_pos r with rfl | hpos
    · unfold evalLift
      cases f <;> rfl
    · obtain ⟨hp, -⟩ := par_facts hr (by omega)
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      unfold evalLift
      simp only [evalLiftF, if_neg (Nat.succ_ne_zero r')]
      rw [ih _ hp (by omega) f' (by omega), ih _ hp (by omega) r' (by omega)]

noncomputable abbrev FLf := at0 CFSG.KD.HNPt15020.FL
noncomputable abbrev ILf := at0 CFSG.KD.HNPt15020.IL
noncomputable abbrev MIf := at0 CFSG.KD.HNPt15020.MI
noncomputable abbrev NCf := at0 CFSG.KD.HNPt15020.NC

theorem step_img {s m x y : Nat}
    (h : stepK FLf ILf MIf NCf 63 s m x y = true) {g : RH} (hW : Canon 5 133 13 (MX m))
    (hg : OM (MX m) = matR g) : ∃ hx : x < nPts, y < nPts ∧ ((g • (⟨x, hx⟩ : X) : X) : ℕ) = y := by
  unfold stepK at h
  simp only [strictB_eq', bAnd_eq', Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hc, hi, hm, hx, hy⟩ := h
  have hck := chK.all _ hc
  unfold ch chunkK at hck
  simp only [bAnd_eq', Bool.and_eq_true] at hck
  obtain ⟨h64, hpts, himg⟩ := hck
  have h64' : at0 CFSG.KD.HNPt15020.NC (Nat.shiftRight s 6) ≤ 64 := Nat.ble_eq.mp h64
  have hp := allN_spec hpts _ hi
  simp only [bAnd_eq', Bool.and_eq_true, Nat.blt_eq] at hp
  have hm' : at0 CFSG.KD.HNPt15020.MI (Nat.shiftRight s 6) = m := Nat.eq_of_beq_eq_true hm
  rw [hm'] at himg
  rw [← Nat.eq_of_beq_eq_true hx, ← Nat.eq_of_beq_eq_true hy]
  refine ⟨hp.1, hp.2, ?_⟩
  exact ri_pts hW hg h64' himg hi hp.1 hp.2

theorem wt_mat {i : Nat} (hi : i < 14) :
    Canon 5 133 13 (MX i) ∧ OM (MX i) = matR (wordG pWords[i]!) := by
  have e : MX i = CFSG.KD.HNPt2086.WT i := by
    unfold MX
    rw [show Nat.blt i 14 = true from Nat.blt_eq.mpr hi]
  rw [e]
  exact HNPt2086.WT_mat hi

local notation "TJ" => gTabsJ
local notation "TiJ" => pinvs nPts gTabsJ

theorem fact_ok :
    ∀ j < 2620, f21 CFSG.KD.HNPt15020.FR j < 16384 ∧
      evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.FR j) (f21 CFSG.KD.HNPt15020.FX j) =
        f21 CFSG.KD.HNPt15020.FY j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have h := sliceK_spec (S := 41) (by norm_num) (by norm_num) (fun s hs => fcK.all s hs) j hj
    unfold factK at h
    simp only [strictB_eq', bAnd_eq'] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hr, hx, hy, h⟩ := h
    have hr : f21 CFSG.KD.HNPt15020.FR j < 16384 := Nat.blt_eq.mp hr
    refine ⟨hr, ?_⟩
    rw [bIf_eq'] at h
    by_cases r0 : f21 CFSG.KD.HNPt15020.FR j = 0
    · rw [if_pos (by rw [r0]; rfl)] at h
      rw [r0, Nat.eq_of_beq_eq_true h]
      rfl
    · rw [if_neg (fun e => r0 (Nat.eq_of_beq_eq_true e))] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hp, hpr, hpx, hst⟩ := h
      have hp : f21 CFSG.KD.HNPt15020.FP j < j := Nat.blt_eq.mp hp
      obtain ⟨pl, ll, ep, el⟩ := par_facts hr r0
      obtain ⟨-, ihp⟩ := ih _ hp (by omega)
      rw [Nat.eq_of_beq_eq_true hpr, ← ep, Nat.eq_of_beq_eq_true hpx] at ihp
      rw [← el] at hst
      obtain ⟨cW, mW⟩ := wt_mat ll
      obtain ⟨hx', hy', e⟩ := step_img hst cW mW
      generalize hR : f21 CFSG.KD.HNPt15020.FR j = r at *
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      unfold evalLift
      simp only [evalLiftF, if_neg (Nat.succ_ne_zero r')]
      rw [lift_fuel _ _ _ _ (by omega) r' (by omega), ihp,
        evalWordPt_eq HNPt2086.hT HNPt2086.hTi _ (HNPt2086.pw_data _ ll).2.2 ⟨_, hx'⟩]
      exact e

theorem eqNL_eq : ∀ l m : List Nat, eqNL l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by simp [eqNL])
  | _ :: _, [], h => absurd h (by simp [eqNL])
  | a :: l, b :: m, h => by
    change bAnd(Nat.beq a b, eqNL l m) = true at h
    rw [bAnd_eq', Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqNL_eq l m h.2]

theorem codes_eq {s L : Nat} (h : letsK HNT4T.QN s L = true) :
    codesAt s L = (wordAt HNT4T.QN s L).map gcode := by
  unfold codesAt wordAt
  rw [List.map_map]
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨h1, h2⟩ := letsK_spec h x hx
  simp only [Function.comp, gcode, sub11]
  rw [if_pos (by omega)]
  change x - 12 = ((x : Int) - 11).toNat - 1
  omega

theorem letR_neg {l : Int}
    (hl : l ≠ 0 ∧ l.natAbs ≤ 11) : letR (gcode (-l)) = (letR (gcode l))⁻¹ := by
  rw [letR_gcode hl, letR_gcode ⟨by omega, by omega⟩]
  by_cases hp : 0 < l
  · rw [if_pos hp, if_neg (by omega), neg_neg]
  · rw [if_neg hp, if_pos (by omega), inv_inv]

theorem wordG_invW {w : List Int}
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 11) : wordG (invW w) = (wordG w)⁻¹ := by
  unfold wordG invW
  rw [List.prod_inv_reverse, List.map_reverse, List.map_reverse]
  simp only [List.map_map]
  congr 2
  refine List.map_congr_left fun l hl => ?_
  simp only [Function.comp]
  exact letR_neg (hw l hl)

theorem wordG_append (a b : List Int) :
    wordG (a ++ b) = wordG a * wordG b := by
  unfold wordG
  rw [List.map_append, List.map_append, List.prod_append]

theorem om_inv {A B : Nat} {g : RH}
    (hA : Canon 5 133 13 A) (hB : Canon 5 133 13 B) (hg : OM A = matR g)
    (h : Nat.beq (HN.mm A B) CFSG.KD.OrdHN.ONE = true) : OM B = matR g⁻¹ := by
  have e := congrArg OM (Nat.eq_of_beq_eq_true h)
  rw [(HNXP.mm_sound hA hB).2, HNXP.one_ord, hg] at e
  calc OM B = matR g⁻¹ * (matR g * OM B) := by
        rw [← Matrix.mul_assoc, ← matR_mul, inv_mul_cancel, matR_one, Matrix.one_mul]
    _ = matR g⁻¹ := by rw [e, Matrix.mul_one]

theorem word_mat {w : List Int}
    (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 10) :
    Canon 5 133 13 (wordC CFSG.KD.HNPtC.GT (w.map gcode)) ∧
      OM (wordC CFSG.KD.HNPtC.GT (w.map gcode)) = matR (wordG w) := by
  have hc : ∀ c ∈ w.map gcode, c < 22 := by
    intro c hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
    obtain ⟨h1, h2⟩ := hw l hl
    unfold gcode
    rw [if_pos (by omega)]
    omega
  exact wordGT_mat _ hc

theorem lets11 {w : List Int} (hw : ∀ l ∈ w, 1 ≤ l ∧ l ≤ 10) : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 11 :=
  fun l hl => ⟨by have := hw l hl; omega, by have := hw l hl; omega⟩

theorem lets11_inv {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 11) :
    ∀ l ∈ invW w, l ≠ 0 ∧ l.natAbs ≤ 11 := by
  intro l hl
  unfold invW at hl
  rw [List.mem_reverse] at hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
  have := hw x hx
  omega

theorem comm_lets {u v : List Int} (hu : ∀ l ∈ u, 1 ≤ l ∧ l ≤ 10) (hv : ∀ l ∈ v, 1 ≤ l ∧ l ≤ 10) :
    ∀ l ∈ commW u v, l ≠ 0 ∧ l.natAbs ≤ 11 := by
  intro l hl
  unfold commW at hl
  simp only [List.mem_append] at hl
  rcases hl with ((h | h) | h) | h
  · exact lets11 hu l h
  · exact lets11 hv l h
  · exact lets11_inv (lets11 hu) l h
  · exact lets11_inv (lets11 hv) l h

theorem cm_mat {f : Nat} (hf : f < 9) :
    Canon 5 133 13 (MX (14 + f)) ∧
      OM (MX (14 + f)) = matR (wordG (commW (poolRec HNT4T.QN HNT4T.QP f).1
        (poolRec HNT4T.QN HNT4T.QP f).2)) ∧
    Canon 5 133 13 (MX (23 + f)) ∧
      OM (MX (23 + f)) = matR (wordG (invW (commW (poolRec HNT4T.QN HNT4T.QP f).1
        (poolRec HNT4T.QN HNT4T.QP f).2))) := by
  have h := mtK.all f hf
  unfold mt at h
  simp only [strictB_eq', bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨hu, hv, hU, hV, vUI, vVI, vCI, iU, iV, hC, iC⟩ := h
  have hl := allN_spec HNT4S.letQ f (by omega)
  unfold poolLetK at hl
  rw [strictB_eq', bAnd_eq', Bool.and_eq_true] at hl
  obtain ⟨lu, lv⟩ := pool_lets (f := f) (by omega)
  set u := (poolRec HNT4T.QN HNT4T.QP f).1 with hu_def
  set v := (poolRec HNT4T.QN HNT4T.QP f).2 with hv_def
  have eu : CFSG.KD.HNPt15020.uc.getD f [] = u.map gcode := by
    rw [eqNL_eq _ _ hu, codes_eq hl.1]
    rfl
  have ev : CFSG.KD.HNPt15020.vc.getD f [] = v.map gcode := by
    rw [eqNL_eq _ _ hv, codes_eq hl.2]
    rfl
  rw [eu] at hU
  rw [ev] at hV
  obtain ⟨cU, mU⟩ := word_mat lu
  obtain ⟨cV, mV⟩ := word_mat lv
  rw [Nat.eq_of_beq_eq_true hU] at cU mU
  rw [Nat.eq_of_beq_eq_true hV] at cV mV
  have cUI := HNXP.canon_of_validHN vUI
  have cVI := HNXP.canon_of_validHN vVI
  have cCI := HNXP.canon_of_validHN vCI
  have mUI := om_inv cU cUI mU iU
  have mVI := om_inv cV cVI mV iV
  have c1 := HNXP.mm_sound cU cV
  have c2 := HNXP.mm_sound c1.1 cUI
  have c3 := HNXP.mm_sound c2.1 cVI
  rw [Nat.eq_of_beq_eq_true hC] at c3
  have mC : OM (at0 CFSG.KD.HNPt15020.CM f) = matR (wordG (commW u v)) := by
    rw [c3.2, c2.2, c1.2, mU, mV, mUI, mVI, ← wordG_invW (lets11 lu), ← wordG_invW (lets11 lv),
      ← matR_mul, ← matR_mul, ← matR_mul, commW, wordG_append, wordG_append, wordG_append]
  have mCI := om_inv c3.1 cCI mC iC
  rw [← wordG_invW (comm_lets lu lv)] at mCI
  have bf : ∀ {a b : Nat}, b ≤ a → Nat.blt a b = false := fun h =>
    Bool.eq_false_iff.mpr fun e => absurd (Nat.blt_eq.mp e) (by omega)
  have e1 : MX (14 + f) = at0 CFSG.KD.HNPt15020.CM f := by
    unfold MX
    rw [bf (by omega : 14 ≤ 14 + f), show Nat.blt (14 + f) 23 = true from Nat.blt_eq.mpr (by omega)]
    change at0 CFSG.KD.HNPt15020.CM (Nat.sub (14 + f) 14) = _
    rw [show Nat.sub (14 + f) 14 = f from Nat.add_sub_cancel_left 14 f]
  have e2 : MX (23 + f) = at0 CFSG.KD.HNPt15020.CIM f := by
    unfold MX
    rw [bf (by omega : 14 ≤ 23 + f), bf (by omega : 23 ≤ 23 + f)]
    change at0 CFSG.KD.HNPt15020.CIM (Nat.sub (23 + f) 23) = _
    rw [show Nat.sub (23 + f) 23 = f from Nat.add_sub_cancel_left 23 f]
  rw [e1, e2]
  exact ⟨c3.1, mC, cCI, mCI⟩

theorem fact_get
    {b k x y : Nat} (hb : b < 2620)
    (h1 : f21 CFSG.KD.HNPt15020.FR b = k) (h2 : f21 CFSG.KD.HNPt15020.FX b = x)
    (h3 : f21 CFSG.KD.HNPt15020.FY b = y) : evalLift TJ TiJ InvData.parRecs k x = y := by
  rw [← h1, ← h2, ← h3]
  exact (fact_ok b hb).2

noncomputable abbrev aq (a j : Nat) : Nat := f21 CFSG.KD.HNPt15020.AQ (9 * a + j)

theorem faith_ok
    {a : Nat} (ha : a < 135) :
    f21 CFSG.KD.HNPt15020.AF a < 9 ∧
    evalZT4 TJ TiJ (f21 CFSG.KD.HNPt15020.AK a) (poolRec HNT4T.QN HNT4T.QP (f21 CFSG.KD.HNPt15020.AF a))
      (evalZT4 TJ TiJ (f21 CFSG.KD.HNPt15020.AK a)
        (poolRec HNT4T.QN HNT4T.QP (f21 CFSG.KD.HNPt15020.AF a))
        (f21 CFSG.KD.HNPt15020.AQ (9 * a))) ≠ f21 CFSG.KD.HNPt15020.AQ (9 * a) := by
  have h := allN_spec faK a ha
  unfold faithK at h
  simp only [strictB_eq', bAnd_eq', Nat.add_eq, Nat.mul_eq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hf, hs, hne⟩ := h
  have hf' : f21 CFSG.KD.HNPt15020.AF a < 9 := Nat.blt_eq.mp hf
  refine ⟨hf', ?_⟩
  obtain ⟨cC, mC, cCI, mCI⟩ := cm_mat hf'
  have hlets := pool_lets (f := f21 CFSG.KD.HNPt15020.AF a) (by omega)
  have hcl := comm_lets hlets.1 hlets.2
  have st : ∀ i < 4, evalWordPt TJ TiJ (if i % 2 = 0 then
        invW (commW (poolRec HNT4T.QN HNT4T.QP (f21 CFSG.KD.HNPt15020.AF a)).1
          (poolRec HNT4T.QN HNT4T.QP (f21 CFSG.KD.HNPt15020.AF a)).2) else
        commW (poolRec HNT4T.QN HNT4T.QP (f21 CFSG.KD.HNPt15020.AF a)).1
          (poolRec HNT4T.QN HNT4T.QP (f21 CFSG.KD.HNPt15020.AF a)).2) (aq a (2 * i)) =
        aq a (2 * i + 1) ∧
      evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.AK a) (aq a (2 * i + 1)) =
        aq a (2 * i + 2) := by
    intro i hi
    have hi' := allN_spec hs i hi
    simp only [Bool.and_eq_true, Nat.blt_eq] at hi'
    obtain ⟨hst, hb, h1, h2, h3⟩ := hi'
    refine ⟨?_, fact_get hb (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
      (Nat.eq_of_beq_eq_true h3)⟩
    by_cases ev : i % 2 = 0
    · rw [if_pos ev]
      have e : nIf(Nat.beq (Nat.land i 1) 0, 23 + f21 CFSG.KD.HNPt15020.AF a,
          14 + f21 CFSG.KD.HNPt15020.AF a) = 23 + f21 CFSG.KD.HNPt15020.AF a := by
        rw [show Nat.land i 1 = i % 2 from Nat.and_one_is_mod i, ev]
        rfl
      rw [e] at hst
      obtain ⟨hx, -, e⟩ := step_img hst cCI mCI
      exact (evalWordPt_eq HNPt2086.hT HNPt2086.hTi _ (lets11_inv hcl) ⟨_, hx⟩).trans e
    · rw [if_neg ev]
      have e : nIf(Nat.beq (Nat.land i 1) 0, 23 + f21 CFSG.KD.HNPt15020.AF a,
          14 + f21 CFSG.KD.HNPt15020.AF a) = 14 + f21 CFSG.KD.HNPt15020.AF a := by
        rw [show Nat.land i 1 = i % 2 from Nat.and_one_is_mod i, show i % 2 = 1 by omega]
        rfl
      rw [e] at hst
      obtain ⟨hx, -, e⟩ := step_img hst cC mC
      exact (evalWordPt_eq HNPt2086.hT HNPt2086.hTi _ hcl ⟨_, hx⟩).trans e
  have a0 := (st 0 (by norm_num)).1
  have b0 := (st 0 (by norm_num)).2
  have a1 := (st 1 (by norm_num)).1
  have b1 := (st 1 (by norm_num)).2
  have a2 := (st 2 (by norm_num)).1
  have b2 := (st 2 (by norm_num)).2
  have a3 := (st 3 (by norm_num)).1
  have b3 := (st 3 (by norm_num)).2
  simp only [show (2 * 0) % 2 = 0 from rfl, show 0 % 2 = 0 from rfl, show 1 % 2 = 1 from rfl,
    show 2 % 2 = 0 from rfl, show 3 % 2 = 1 from rfl, if_pos, if_neg, reduceIte,
    Nat.reduceMul, Nat.reduceAdd, one_ne_zero] at a0 a1 a2 a3 b0 b1 b2 b3
  have e0 : f21 CFSG.KD.HNPt15020.AQ (9 * a) = aq a 0 := rfl
  rw [e0]
  unfold evalZT4
  rw [a0, b0, a1, b1, a2, b2, a3, b3]
  intro e
  have e' : f21 CFSG.KD.HNPt15020.AQ (9 * a + 8) = f21 CFSG.KD.HNPt15020.AQ (9 * a) := e
  rw [e', Nat.beq_refl] at hne
  exact absurd hne (by decide)

theorem noInv_ok
    {a : Nat} (ha : a < 120) :
    evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.NK a)
      (evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.NK a)
        (f21 CFSG.KD.HNPt15020.NQ (3 * a))) ≠ f21 CFSG.KD.HNPt15020.NQ (3 * a) := by
  have h := allN_spec niK a ha
  unfold noInvK at h
  simp only [strictB_eq', bAnd_eq', Nat.add_eq, Nat.mul_eq] at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hs, hne⟩ := h
  have st : ∀ i < 2, evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.NK a)
      (f21 CFSG.KD.HNPt15020.NQ (3 * a + i)) = f21 CFSG.KD.HNPt15020.NQ (3 * a + i + 1) := by
    intro i hi
    have hi' := allN_spec hs i hi
    simp only [Bool.and_eq_true, Nat.blt_eq] at hi'
    obtain ⟨hb, h1, h2, h3⟩ := hi'
    exact fact_get hb (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
      (Nat.eq_of_beq_eq_true h3)
  have s0 : evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.NK a)
      (f21 CFSG.KD.HNPt15020.NQ (3 * a)) = f21 CFSG.KD.HNPt15020.NQ (3 * a + 1) := st 0 (by norm_num)
  have s1 : evalLift TJ TiJ InvData.parRecs (f21 CFSG.KD.HNPt15020.NK a)
      (f21 CFSG.KD.HNPt15020.NQ (3 * a + 1)) = f21 CFSG.KD.HNPt15020.NQ (3 * a + 2) :=
    st 1 (by norm_num)
  rw [s0, s1]
  intro e
  rw [e, Nat.beq_refl] at hne
  exact absurd hne (by decide)

theorem mp_ok {k : Nat} (hk : k < 16384) :
    mapK HNT4T.WN HNT4T.WP 135 120 CFSG.KD.HNPt15020.AK CFSG.KD.HNPt15020.AF
      CFSG.KD.HNPt15020.AQ CFSG.KD.HNPt15020.NK CFSG.KD.HNPt15020.NQ CFSG.KD.HNPt15020.TK k = true :=
  sliceK_spec (L := 64) (S := 256) (by norm_num) (by norm_num) (fun s hs => mpK.all s hs) k hk

theorem cs_size : (poolT4 (decodePoolT4 hnT4PoolStr)).size = 64 := by
  unfold poolT4
  rw [Array.size_map, pool_size]

theorem zs_unpack {k : Nat} (hk : k < 16384) (fs : List Nat) (hfs : ∀ f ∈ fs, f < 64) :
    fs.map (fun f => zT4 pE[k]! (poolT4 (decodePoolT4 hnT4PoolStr))[f]!) =
      (fs.map fun f => zP (HPE.T k) (HNT4C.P f) (HNT4C.Q f)).map (unpack 800 10) ∧
    ∀ a ∈ fs.map (fun f => zP (HPE.T k) (HNT4C.P f) (HNT4C.Q f)), Cn a := by
  have hT : Cn (HPE.T k) := HN2088.T_canon k hk
  refine ⟨?_, fun a ha => ?_⟩
  · rw [List.map_map]
    refine List.map_congr_left fun f hf => ?_
    obtain ⟨e, c1, c2⟩ := cm_facts (hfs f hf)
    rw [pE_get hk, e]
    exact zT4_unpack hT c1 c2
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
    obtain ⟨-, c1, c2⟩ := cm_facts (hfs f hf)
    exact cn_zP hT c1 c2

theorem wit_ok
    {k : Nat} (hk : k < 16384) :
    t4WitOK TJ TiJ pE (decodePoolT4 hnT4PoolStr) (poolT4 (decodePoolT4 hnT4PoolStr)) k
      (decodeT4 hnT4WitStr)[k]! = true := by
  rw [wits_get hk]
  have hm := mp_ok hk
  unfold mapK at hm
  simp only [strictB_eq', bAnd_eq'] at hm
  simp only [bIf_eq'] at hm
  rcases t4WK_spec (wt_ok hk) with ⟨c, hs⟩ | ⟨c, hfs, hord⟩ | ⟨c, hf, hp, hz⟩ | ⟨c, hp⟩
  · unfold t4Wit
    rw [if_pos c]
    unfold t4WitOK isInvP
    rw [pE_get hk, ← HN2088.EA_get hk]
    rcases hs with rfl | hsq
    · rw [HN2088.EA_zero, HN2088.peq_self]
      rfl
    · have hsq' : CFSG.KS.BaseEq.sqFixK 10 (mask 10) HN2088.bp (HPE.T k) = false := hsq
      rw [HN2088.sq_iff hk, hsq']
      simp
  · unfold t4Wit
    rw [if_neg (by omega), if_pos c]
    unfold t4WitOK
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨fun f hf => by rw [cs_size]; exact hfs f hf, ?_⟩
    obtain ⟨e1, hc⟩ := zs_unpack hk _ hfs
    rw [e1]
    obtain ⟨e2, c2⟩ := prodP_unpack _ hc
    rw [e2]
    obtain ⟨e3, c3⟩ := powP_unpack c2 _
    rw [e3]
    exact ord4P_unpack c3 hord
  · unfold t4Wit
    rw [if_neg (by omega), if_neg (by omega), if_pos c]
    rw [if_pos (by rw [c]; rfl)] at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨ht, hak, haf, haq⟩ := hm
    have ht' := Nat.blt_eq.mp ht
    obtain ⟨-, hX⟩ := faith_ok ht'
    rw [Nat.eq_of_beq_eq_true hak, Nat.eq_of_beq_eq_true haf] at hX
    have haq' : f21 CFSG.KD.HNPt15020.AQ (9 * f21 CFSG.KD.HNPt15020.TK k) =
      HNT4T.WN (HNT4T.WP k + 2) := Nat.eq_of_beq_eq_true haq
    rw [haq'] at hX
    unfold t4WitOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    obtain ⟨e, c1, c2⟩ := cm_facts hf
    have hT : Cn (HPE.T k) := HN2088.T_canon k hk
    refine ⟨⟨⟨(by rw [pool_size]; exact hf), (by rw [hns_n]; exact hp)⟩, ?_⟩, ?_⟩
    · rw [pE_get hk, e, zT4_unpack hT c1 c2, pcomp_unpack (cn_zP hT c1 c2) (cn_zP hT c1 c2),
        pid_unpack, peq_unpack (cn_pcomp (cn_zP hT c1 c2) (cn_zP hT c1 c2)) cn_id, hz]
      exact Nat.beq_refl _
    · rw [pool_get hf]
      exact hX
  · have c0 : HNT4T.WN (HNT4T.WP k) ≠ 0 := by omega
    unfold t4Wit
    rw [if_neg c0, if_neg (by omega), if_neg (by omega)]
    rw [if_neg (by rw [c]; decide), if_pos (by rw [c]; rfl)] at hm
    simp only [Bool.and_eq_true] at hm
    obtain ⟨ht, hnk, hnq⟩ := hm
    have hX := noInv_ok (Nat.blt_eq.mp ht)
    rw [Nat.eq_of_beq_eq_true hnk] at hX
    have hnq' : f21 CFSG.KD.HNPt15020.NQ (3 * f21 CFSG.KD.HNPt15020.TK k) =
      HNT4T.WN (HNT4T.WP k + 1) := Nat.eq_of_beq_eq_true hnq
    rw [hnq'] at hX
    unfold t4WitOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
    exact ⟨by rw [hns_n]; exact hp, hX⟩

theorem hn_t4_ok :
    hnT4Check (decodePoolT4 hnT4PoolStr) (decodeT4 hnT4WitStr) = true := by
  have eT : gTabs = gTabsJ := by
    unfold gTabs
    rw [hStrongArr_SJ, hns_n, natTab_alpha, natTab_beta]
  unfold hnT4Check t4Run t4Loop
  rw [eT, hns_n]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, by rw [wits_eq, Array.size_ofFn]⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    rw [pool_size] at hi
    rw [← getElem!_pos _ i (by rw [pool_size]; exact hi), pool_get hi]
    simp only [Bool.and_eq_true]
    exact ⟨plettersOK_of (pool_lets hi).1, plettersOK_of (pool_lets hi).2⟩
  · exact allBelowN_iff.2 fun k hk => wit_ok hk

end CertificateChecks.KernelSporSch.HNPt15020

end

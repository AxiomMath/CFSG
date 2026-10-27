
module

public import Certificates.Kernel.LocalComp.Census.Pin
public import Certificates.Kernel.LocalComp.Census.Mats
public import Certificates.Kernel.LocalComp.SHatClosed.Enum
public import CFSG.Certificates.Kernel.SpanPinSound
public import CFSG.Certificates.Kernel.LocalCompPinSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.Spor.MulHSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.CensusC

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.KC.SpanPin CFSG.KC.CensusForm CFSG.KS.Raw.Orb
open CFSG.ComponentClassification.AS81.Census CFSG.PSL3Four.Native
open CertificateChecks.KernelLC.CensusD CertificateChecks.KernelLC.CensusM

theorem rref_n0 : rrefK 6 12 4095 72 (N0K 0) = true := by quickRfl

theorem roots_ok : allN 20 (fun j => mapsK 6 12 4095 72
    (img (ML (Nat.add 9 (Nat.mul 2 j))) (MH (Nat.add 9 (Nat.mul 2 j)))) (N0K 0) (Kf (OF j))) =
    true := by quickRfl

theorem good_maps : allN 3 (fun e => strictB (Kf (OF (goodData[e]!).1)) fun k =>
    mapsK 6 12 4095 72 (img (ML 0) (MH 0)) k k) = true := by quickRfl

theorem bad_maps : allN 32 (fun e => mapsK 6 12 4095 72
    (img (ML (Nat.add 55 e)) (MH (Nat.add 55 e))) (N0K 0) (Kf (BQ e))) = true := by quickRfl

theorem eq_tabs : (Nat.beq (G1L 0) (ML 5) && Nat.beq (G1H 0) (MH 5) && Nat.beq (G2L 0) (ML 6) &&
    Nat.beq (G2H 0) (MH 6) && Nat.beq (B3L 0) (ML 3) && Nat.beq (B3H 0) (MH 3) &&
    Nat.beq (B5L 0) (ML 4) && Nat.beq (B5H 0) (MH 4)) = true := by quickRfl

@[expose] noncomputable def nsl (j : Nat) : Nat := (CN j + 1259) / 1260

@[expose] noncomputable def sb (j : Nat) : Nat := (List.range j).foldl (fun a i => a + nsl i) 0

theorem orbit_facts : ∀ j < 20, 0 < CN j ∧ CN j ≤ 20160 ∧ OF j + CN j ≤ 48960 ∧
    CN j ≤ 1260 * nsl j ∧ ∀ t < nsl j, sb j + t < 48 ∧ SJ (sb j + t) = j ∧ ST (sb j + t) = t := by
  decide +kernel

theorem orbit_sep : ∀ j < 20, ∀ j' < 20, j < j' → OF j + CN j ≤ OF j' := by decide +kernel

theorem sum_cn : (List.range 20).foldl (fun s j => s + CN j) 0 = 48960 := by decide +kernel

theorem bad_idx : ∀ e < 32, BJ e ∈ goodOrbits ∧ BJ e < 20 ∧ OF (BJ e) ≤ BQ e ∧
    BQ e < OF (BJ e) + CN (BJ e) := by decide +kernel

theorem n0_span : n0Tab = spanTab 6 12 4095 (N0K 0) := by
  have h : ∀ s < 64, f2code s = spanOf 6 12 4095 (N0K 0) s := by decide +kernel
  have hl : (List.range 64).map f2code = (List.range 64).map (spanOf 6 12 4095 (N0K 0)) :=
    List.map_congr_left fun s hs => h s (List.mem_range.1 hs)
  unfold n0Tab spanTab spanList
  have e : (2 : Nat) ^ 6 = 64 := rfl
  rw [e, hl]

theorem rows_ptK {j : Nat} (hj : j < 20) :
    ∀ i < CN j, ptK 6 12 4095 72 6 63 2 At Bt Kf Wf Xf (OF j) (CN j) i = true := by
  obtain ⟨-, -, -, hcS, hsl⟩ := orbit_facts j hj
  refine ptK_of_slices (L := 1260) (S := nsl j) hcS fun t ht => ?_
  obtain ⟨hlt, hJ, hT⟩ := hsl t ht
  have h := CensusS.all (sb j + t) hlt
  unfold slC at h
  rw [strictB_eq, strictB_eq, hJ, hT] at h
  exact h

theorem key_facts {j i : Nat} (hj : j < 20) (hi : i < CN j) :
    Rref 6 12 4095 72 (Kf (OF j + i)) ∧ Xf (Kf (OF j + i)) = true :=
  ptK_key (rows_ptK hj i hi)

theorem key_inj : ∀ a < 48960, ∀ b < 48960, Kf a = Kf b → a = b :=
  inj_of_sortK (L := 4896) (S := 10) (by norm_num) fun s hs => CensusR.all s hs

theorem tabs_eq' : G1L 0 = ML 5 ∧ G1H 0 = MH 5 ∧ G2L 0 = ML 6 ∧ G2H 0 = MH 6 ∧ B3L 0 = ML 3 ∧
    B3H 0 = MH 3 ∧ B5L 0 = ML 4 ∧ B5H 0 = MH 4 := by
  have h := eq_tabs
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩, e6⟩, e7⟩, e8⟩ := h
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩

theorem tab_at {i : Nat} (hi : i < 87) : tabK (unpackM (IM i)) (MB i) (ML i) (MH i) = true :=
  CensusT.all i hi

theorem step_ok {l : Nat} (hl : l < 2) {Kh Kq : Nat} (Rh : Rref 6 12 4095 72 Kh)
    (Rq : Rref 6 12 4095 72 Kq)
    (hmap : mapsK 6 12 4095 72 (img2 12 4095 6 63 (At l) (Bt l)) Kh Kq = true) :
    orbitStep l (spanTab 6 12 4095 Kh) = spanTab 6 12 4095 Kq := by
  obtain ⟨e1, e2, e3, e4, -⟩ := tabs_eq'
  interval_cases l
  · have hm : mapsK 6 12 4095 72 (img (ML 5) (MH 5)) Kh Kq = true := by
      rw [← e1, ← e2]
      exact hmap
    have ht := tab_at (i := 5) (by norm_num)
    have hi := isom_IM (i := 5) (by norm_num)
    rw [← b_g1] at ht hi
    unfold orbitStep g1T
    simp only [↓reduceIte]
    exact formStepT_span ht hi Rh Rq hm
  · have hm : mapsK 6 12 4095 72 (img (ML 6) (MH 6)) Kh Kq = true := by
      rw [← e3, ← e4]
      exact hmap
    have ht := tab_at (i := 6) (by norm_num)
    have hi := isom_IM (i := 6) (by norm_num)
    rw [← b_g2] at ht hi
    unfold orbitStep g2T
    simp only [one_ne_zero, ↓reduceIte]
    exact formStepT_span ht hi Rh Rq hm

theorem root_span {j : Nat} (hj : j < 20) : spanTab 6 12 4095 (Kf (OF j)) = rootForm j := by
  have R0 := (key_facts hj (orbit_facts j hj).1).1
  rw [Nat.add_zero] at R0
  have hm := CFSG.KS.allN_spec roots_ok j hj
  have ht := tab_at (i := 9 + 2 * j) (by omega)
  have hi := isom_IM (i := 9 + 2 * j) (by omega)
  rw [← (b_root j hj).1] at ht hi
  unfold rootForm
  rw [n0_span]
  exact (formStep_span ht hi (rref_of rref_n0) R0 hm).symm

theorem orbits_get {j : Nat} (hj : j < 20) : orbits[j]! = bfs orbitStep 2 (rootForm j) 20160 := by
  unfold orbits
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map, Array.getElem_range]

theorem orbit_bfs {j : Nat} (hj : j < 20) :
    orbits[j]! = ⟨Array.ofFn (n := CN j) fun i => spanTab 6 12 4095 (Kf (OF j + i.val)),
      Array.ofFn (n := CN j) fun i => wf (Wf (OF j + i.val)) 2,
      Array.ofFn (n := CN j) fun i => wf (Wf (OF j + i.val)) (2 + 1)⟩ ∧
    treeOK orbitStep 2 (rootForm j) orbits[j]! = true := by
  obtain ⟨hc, hcap, hN, -, -⟩ := orbit_facts j hj
  have h := spanPin_bfs (cap := 20160) (step := orbitStep) (root := rootForm j) rfl rfl
    (rows_ptK hj) hc hcap
    (fun a ha b hb e => by have := key_inj _ (by omega) _ (by omega) e; omega)
    (fun l hl Kh Kq Rh Rq hm => step_ok hl Rh Rq hm) (root_span hj)
  rw [orbits_get hj]
  exact ⟨h.1, by rw [h.1]; exact h.2⟩

theorem tabs_eq {j : Nat} (hj : j < 20) :
    (orbits[j]!).tabs = Array.ofFn (n := CN j) fun i => spanTab 6 12 4095 (Kf (OF j + i.val)) := by
  rw [(orbit_bfs hj).1]

theorem mem_tabs {j : Nat} (hj : j < 20) {t : Tab} :
    t ∈ (orbits[j]!).tabs ↔ ∃ i < CN j, spanTab 6 12 4095 (Kf (OF j + i)) = t := by
  rw [tabs_eq hj, Array.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem disj : ∀ j < 20, ∀ j' < 20, ∀ t ∈ (orbits[j]!).tabs, t ∈ (orbits[j']!).tabs → j = j' := by
  intro j hj j' hj' t ht ht'
  obtain ⟨i, hi, rfl⟩ := (mem_tabs hj).1 ht
  obtain ⟨i', hi', e⟩ := (mem_tabs hj').1 ht'
  have hk := spanTab_inj rfl rfl (key_facts hj' hi').1 (key_facts hj hi).1 e
  have h1 := (orbit_facts j hj).2.2.1
  have h2 := (orbit_facts j' hj').2.2.1
  have := key_inj _ (by omega) _ (by omega) hk
  rcases Nat.lt_trichotomy j j' with h | h | h
  · have := orbit_sep j hj j' hj' h
    omega
  · exact h
  · have := orbit_sep j' hj' j hj h
    omega

theorem foldl_sum_congr {f g : Nat → Nat} : ∀ (l : List Nat) (a : Nat), (∀ j ∈ l, f j = g j) →
    l.foldl (fun s j => s + f j) a = l.foldl (fun s j => s + g j) a
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h x List.mem_cons_self]
    exact foldl_sum_congr l _ fun j hj => h j (List.mem_cons_of_mem x hj)

theorem forms_ok : formsOK = true := by
  unfold formsOK
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.ComponentClassification.PSL3Four.allBelow_eq_true,
    Array.all_eq_true]
  refine ⟨⟨⟨by simp [orbits], fun j hj => (orbit_bfs hj).2⟩, ?_⟩, fun j hj i hi => ?_⟩
  · rw [foldl_sum_congr _ _ fun j hj => by
      rw [tabs_eq (List.mem_range.1 hj), Array.size_ofFn]]
    exact sum_cn
  · unfold formIndex
    rw [foldl_insert_get (fun j => (orbits[j]!).tabs) 20 disj j hj _ (Array.getElem_mem hi)]

theorem m1_ok : m1OK = true := by
  unfold m1OK
  rw [CFSG.ComponentClassification.PSL3Four.allBelow_eq_true]
  intro j hj
  rw [Array.all_eq_true_iff_forall_mem]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := (mem_tabs hj).1 ht
  obtain ⟨R, hX⟩ := key_facts hj hi
  obtain ⟨-, -, -, -, e5, e6, e7, e8⟩ := tabs_eq'
  by_cases h3 : formStepT b3T (spanTab 6 12 4095 (Kf (OF j + i))) =
      spanTab 6 12 4095 (Kf (OF j + i))
  · by_cases h5 : formStepT b5T (spanTab 6 12 4095 (Kf (OF j + i))) =
        spanTab 6 12 4095 (Kf (OF j + i))
    · have t3 := tab_at (i := 3) (by norm_num)
      have t5 := tab_at (i := 4) (by norm_num)
      rw [← b_b3] at t3
      rw [← b_b5] at t5
      have m3 := mapsK_of_formStepT t3 R h3
      have m5 := mapsK_of_formStepT t5 R h5
      unfold Xf at hX
      rw [e5, e6, e7, e8, bIf_eq, bIf_eq, bIf_eq, m3, m5] at hX
      have hk : Kf (OF j + i) = N0K 0 := by
        by_contra hne
        have : Nat.beq (Kf (OF j + i)) (N0K 0) = false :=
          Bool.eq_false_iff.mpr fun e => hne (Nat.eq_of_beq_eq_true e)
        rw [this] at hX
        simp at hX
      rw [hk, ← n0_span]
      simp
    · simp [h5]
  · simp [h3]

theorem good_ok : goodOK = true := by
  have hrest : ∀ e < 3, (decide ((goodData[e]!).1 < 20) && f2Mat (goodData[e]!).2.1 &&
      f2Mat (goodData[e]!).2.2 &&
      matMul x0M (goodData[e]!).2.2 == matMul (goodData[e]!).2.2 (goodData[e]!).2.1 &&
      matMul (rootsM[(goodData[e]!).1]!).1 (goodData[e]!).2.1 ==
        matMul x0M (rootsM[(goodData[e]!).1]!).1) = true := by decide +kernel
  unfold goodOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨by decide +kernel, fun x hx => ?_⟩
  obtain ⟨e, he, hxe⟩ := List.getElem_of_mem hx
  have he3 : e < 3 := he
  have hx! : goodData[e]! = x := by rw [getElem!_pos goodData e he]; exact hxe
  have hr := hrest e he3
  obtain ⟨by1, by2⟩ := b_good e he3
  rw [hx!] at hr by1 by2
  rcases x with ⟨j, y, l⟩
  dsimp only at by1 by2
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hr ⊢
  obtain ⟨⟨⟨⟨hj, hfy⟩, hfl⟩, hm1⟩, hm2⟩ := hr
  have hiy : isomOK y = true := by rw [by1]; exact isom_IM (by omega)
  have hil : isomOK l = true := by rw [by2]; exact isom_IM (by omega)
  have hform : formStep x0M (rootForm j) = rootForm j := by
    have hm := CFSG.KS.allN_spec good_maps e he3
    rw [strictB_eq, hx!] at hm
    have R := (key_facts hj (orbit_facts j hj).1).1
    rw [Nat.add_zero] at R
    have ht := tab_at (i := 0) (by norm_num)
    have hi := isom_IM (i := 0) (by norm_num)
    rw [← b_x0] at ht hi
    rw [← root_span hj]
    exact formStep_span ht hi R R hm
  exact ⟨⟨⟨⟨⟨⟨⟨hj, hform⟩, hiy⟩, hfy⟩, hil⟩, hfl⟩, hm1⟩, hm2⟩

theorem bad_ok : badOK = true := by
  have hrest : ∀ e < 32, (decide ((badData[e]!).1 < 20) && decide ((badData[e]!).2.1 < 2) &&
      (badData[e]!).2.2.all (fun a => decide (a < 4)) &&
      matMul (if (badData[e]!).2.1 = 0 then (rootsM[(badData[e]!).1]!).1
          else matMul (rootsM[(badData[e]!).1]!).1 tauM)
        (if (badData[e]!).2.1 = 0 then (rootsM[(badData[e]!).1]!).2
          else matMul tauM (rootsM[(badData[e]!).1]!).2) == idMat) = true := by decide +kernel
  unfold badOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun j hj => by revert j; decide +kernel, fun x hx => ?_⟩
  obtain ⟨e, he, hxe⟩ := List.getElem_of_mem hx
  have he32 : e < 32 := he
  have hx! : badData[e]! = x := by rw [getElem!_pos badData e he]; exact hxe
  have hr := hrest e he32
  have hw := b_bad e he32
  rw [hx!] at hr hw
  obtain ⟨hgo, hj20, hlo, hhi⟩ := bad_idx e he32
  have hmem : spanTab 6 12 4095 (Kf (BQ e)) ∈ (orbits[BJ e]!).tabs := by
    refine (mem_tabs hj20).2 ⟨BQ e - OF (BJ e), by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlo]
  have Rq : Rref 6 12 4095 72 (Kf (BQ e)) := by
    have := (key_facts hj20 (i := BQ e - OF (BJ e)) (by omega)).1
    rwa [Nat.add_sub_cancel' hlo] at this
  have ht := tab_at (i := 55 + e) (by omega)
  have hi := isom_IM (i := 55 + e) (by omega)
  have hstep := formStep_span ht hi (rref_of rref_n0) Rq (CFSG.KS.allN_spec bad_maps e he32)
  rw [← hw, ← n0_span] at hstep
  rcases x with ⟨j, f, w⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    Array.contains_iff_mem] at hr ⊢
  refine ⟨hr.1, hr.2, BJ e, hgo, ?_⟩
  unfold badMatK at hstep
  simp only at hstep
  rw [hstep]
  exact hmem

theorem gens_eq : (#[f2perm g1M, f2perm g2M] : Array (Array Nat)).size = SHatL.ng ∧
    ∀ k < SHatL.ng, (#[f2perm g1M, f2perm g2M] : Array (Array Nat))[k]! =
      CFSG.KS.Raw.unpack 64 7 (SHatL.G k) :=
  CFSG.KC.BfsPin.binds_of_listK rfl (by quickRfl)

theorem lp_ok : (CFSG.KS.Raw.bindListK 64 7 (LP 0) (f2perm tauM).toList &&
    CFSG.KS.Raw.bindListK 64 7 (LP 1) (f2perm cM).toList &&
    CFSG.KS.Prim.canonK 64 7 (CFSG.KS.mask 7) (64 * 7) (LP 0) &&
    CFSG.KS.Prim.canonK 64 7 (CFSG.KS.mask 7) (64 * 7) (LP 1)) = true := by quickRfl

theorem lp_notin : allN 20160 (fun i => bIf(Nat.beq (SHatL.T i) (LP 0), false,
    bIf(Nat.beq (SHatL.T i) (LP 1), false, true))) = true := by quickRfl

theorem not_contains {P : Nat} {x : Array Nat} (hx : x = CFSG.KS.Raw.unpack 64 7 P)
    (hP : CFSG.KS.Prim.canonK 64 7 (CFSG.KS.mask 7) (64 * 7) P = true)
    (hne : ∀ i < 20160, SHatL.T i ≠ P) :
    (Array.ofFn (n := SHatL.N) fun i => CFSG.KS.Raw.unpack 64 7 (SHatL.T i.val)).contains x =
      false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rw [Array.contains_iff_mem, Array.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  have hc := CFSG.KC.BfsPin.bfsK_canon SHatL.ok i.val i.isLt
  have := CFSG.KS.MulH.unpack_injH hc hP (hi.trans hx)
  exact hne i.val i.isLt this

theorem l_ok : lOK = true := by
  obtain ⟨h1, h2⟩ := CFSG.KC.LocalComp.Pin.enumBFS_of_bfsK gens_eq.1 gens_eq.2 SHatL.ok
    (Nat.le_refl _)
  have hl := lp_ok
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨b0, b1⟩, c0⟩, c1⟩ := hl
  have hn := CFSG.KS.allN_spec lp_notin
  unfold lOK lEnum
  have eN : (20160 : Nat) = SHatL.N := rfl
  rw [eN, h1, h2, not_contains (CFSG.KC.BfsPin.eq_unpack_of_bindListK b0) c0 fun i hi e => by
      have := hn i hi
      rw [e, bIf_eq, Nat.beq_refl] at this
      simp at this,
    not_contains (CFSG.KC.BfsPin.eq_unpack_of_bindListK b1) c1 fun i hi e => by
      have := hn i hi
      rw [e, bIf_eq, bIf_eq, Nat.beq_refl] at this
      by_cases h0 : Nat.beq (LP 1) (LP 0) = true
      · rw [h0] at this
        simp at this
      · simp only [Bool.not_eq_true] at h0
        rw [h0] at this
        simp at this]
  simp

theorem mats_ok : matsOK = true := by
  have hiso : ∀ i < 9, isomOK (unpackM (IM i)) = true := fun i hi => isom_IM (by omega)
  have hl : [x0M, tauM, cM, b3M, b5M, g1M, g2M, g1iM, g2iM].all
      (fun M => isomOK M && f2Mat M) = true := by
    rw [b_x0, b_tau, b_c, b_b3, b_b5, b_g1, b_g2, b_g1i, b_g2i]
    simp only [List.all_cons, List.all_nil, hiso 0 (by norm_num), hiso 1 (by norm_num),
      hiso 2 (by norm_num), hiso 3 (by norm_num), hiso 4 (by norm_num), hiso 5 (by norm_num),
      hiso 6 (by norm_num), hiso 7 (by norm_num), hiso 8 (by norm_num), Bool.true_and]
    decide +kernel
  have hprod : ∀ j < 20, (matMul (rootsM[j]!).1 (rootsM[j]!).2 == idMat) = true := by
    decide +kernel
  have hr : (allBelow 20 fun j => isomOK (rootsM[j]!).1 && isomOK (rootsM[j]!).2 &&
      matMul (rootsM[j]!).1 (rootsM[j]!).2 == idMat) = true := by
    rw [CFSG.ComponentClassification.PSL3Four.allBelow_eq_true]
    intro j hj
    rw [(b_root j hj).1, (b_root j hj).2, isom_IM (by omega), isom_IM (by omega), ←
      (b_root j hj).1, ← (b_root j hj).2, hprod j hj]
    rfl
  unfold matsOK
  rw [hl, hr]
  decide +kernel

theorem census_ok : censusCheck = true := by
  unfold censusCheck
  rw [mats_ok, l_ok, forms_ok, m1_ok, good_ok, bad_ok]
  rfl

end CertificateChecks.KernelLC.CensusC

end

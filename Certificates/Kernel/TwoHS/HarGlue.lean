module

public import Certificates.Kernel.TwoHS.Har
public import Certificates.Kernel.TwoHS.FourGlue
public import Certificates.Kernel.TwoHS.HYOpsGlue

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126
open CFSG.KS.MulH CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.TwoHS
open CFSG.Sporadic.Recognition.HSMultiplier

theorem harY_parts (i : Fin 6) :
    harY i = tabT (unpack 11200 14 (HYF i)) ∧ Cn (HYF i) := ⟨harY_eq i, (hy i.isLt).1⟩

theorem harYI_parts (i : Fin 6) :
    harYI i = tabT (unpack 11200 14 (HYF i)) ∧ Cn (HYF i) := by
  refine ⟨?_, (hy i.isLt).1⟩
  unfold harYI
  rw [harY_eq i]
  exact invT_eq (hy i.isLt).2

theorem all_of_strictH {α : Type} (L : List α) (E : α → Nat) (C : Nat → Bool) (e : Nat)
    (he : C e = true) (h : L.all (fun r => strictB (E r) fun v => bIf(Nat.beq v e, true, C v)) = true) :
    L.all (fun r => C (E r)) = true := by
  rw [List.all_eq_true] at h ⊢
  intro r hr
  have h' := h r hr
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h'
  cases hv : Nat.beq (E r) e
  · rw [hv] at h'
    exact h'
  · rw [Nat.eq_of_beq_eq_true hv]
    exact he

theorem hm_cox : hsCoxeter.all (fun r => (List.finRange 6).all fun i =>
    Nat.beq (CFSG.KD.TwoHS.pc (HYF i) (EVK HYF HYF r)) (CFSG.KD.TwoHS.pc (EVK HYF HYF r) (HYF i))) =
      true :=
  all_of_strictH hsCoxeter (EVK HYF HYF) cmH idK hm_idc hm_coxK

theorem hm_extra : hsExtra.all (fun r => (List.finRange 6).all fun i =>
    Nat.beq (CFSG.KD.TwoHS.pc (HYF i) (EVK HYF HYF r)) (CFSG.KD.TwoHS.pc (EVK HYF HYF r) (HYF i))) =
      true :=
  all_of_strictH hsExtra (EVK HYF HYF) cmH idK hm_idc hm_extraK

theorem harModelOK_true : harModelOK = true := by
  have c1 : (List.finRange 6).all (fun i =>
      permOK 11200 (harY i) && invOK 11200 (harY i) (harYI i)) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [(harYI_parts i).1, (harY_parts i).1, permOK_unpack (harY_parts i).2 (hy i.isLt).2,
      invOK_unpack (harY_parts i).2 (harY_parts i).2 (hy i.isLt).2]
    rfl
  have c2 : hsRels.all (fun r => (List.finRange 6).all fun i =>
      commTT 11200 (harY i) (evalW 11200 harY harYI r)) = true := by
    rw [List.all_eq_true]
    intro r hr
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := evalW_eq harY_parts harYI_parts r
    rw [e, (harY_parts i).1, commTT_eq (harY_parts i).2 c]
    rcases List.mem_append.1 hr with h | h
    · exact List.all_eq_true.1 (List.all_eq_true.1 hm_cox r h) i (List.mem_finRange i)
    · exact List.all_eq_true.1 (List.all_eq_true.1 hm_extra r h) i (List.mem_finRange i)
  have c3 : (List.finRange 6).all (fun i =>
      tblEq 11200 (evalW 11200 harY harYI (hsCommWord i)) (harY i)) = true := by
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := evalW_eq harY_parts harYI_parts (hsCommWord i)
    rw [e, (harY_parts i).1, tblEq_eq c (harY_parts i).2]
    exact List.all_eq_true.1 hm_comm i (List.mem_finRange i)
  unfold harModelOK
  rw [c1, c2, c3]
  rfl

theorem hsPGTbls_size : hsPGTbls.size = 2 := rfl

theorem lit_get0 (x y : Table) : (#[x, y] : Array Table)[0]! = x := rfl

theorem lit_get1 (x y : Table) : (#[x, y] : Array Table)[1]! = y := rfl

theorem tabT_map (a : Array Nat) : a.map UInt32.ofNat = tabT a := rfl

theorem hsPGTbls_get {i : Nat} (hi : i < 2) :
    hsPGTbls[i]! = tabT (CFSG.Sporadic.Schreier.hsStrongArrs[i]!) := by
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · unfold hsPGTbls
    rw [lit_get0, tabT_map]
  · unfold hsPGTbls
    rw [lit_get1, tabT_map]

theorem harA_eq (i : Fin 2) : harA i = tabT (unpack 3850 12 (A3 i)) := by
  unfold harA A3
  rw [hsPGTbls_get i.isLt, hsStrong_get i.isLt]

theorem harAI_inv (i : Fin 2) : harAI i = invT 3850 (harA i) := by
  have h1 : i.val < (hsPGTbls.map (invT 3850)).size := by
    rw [Array.size_map, hsPGTbls_size]
    exact i.isLt
  have h2 : i.val < hsPGTbls.size := by
    rw [hsPGTbls_size]
    exact i.isLt
  unfold harAI harA hsPGInvTbls
  rw [getElem!_pos (hsPGTbls.map (invT 3850)) i.val h1, getElem!_pos hsPGTbls i.val h2,
    Array.getElem_map]

theorem hpA (i : Fin 2) : invK (A3 i) = true := List.all_eq_true.1 hp_a i (List.mem_finRange i)

theorem harA_parts (i : Fin 2) : harA i = tabT (unpack 3850 12 (A3 i)) ∧ C3 (A3 i) :=
  ⟨harA_eq i, (invK_spec (hpA i)).1⟩

theorem harAI_parts (i : Fin 2) : harAI i = tabT (unpack 3850 12 (A3I i)) ∧ C3 (A3I i) := by
  refine ⟨?_, (invK_spec (hpA i)).2.1⟩
  rw [harAI_inv i, harA_eq i]
  exact (perm_of (hpA i)).2.1

theorem evalW_foldlG {ι : Type} {n w : Nat} {G GI : ι → Nat} {g gi : ι → Table}
    (hg : ∀ i, g i = tabT (unpack n w (G i)) ∧ canonK n w (mask w) (n * w) (G i) = true)
    (hgi : ∀ i, gi i = tabT (unpack n w (GI i)) ∧ canonK n w (mask w) (n * w) (GI i) = true) :
    ∀ (wd : List (ι × Bool)) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      wd.foldl (fun a l => compT n a (if l.2 then g l.1 else gi l.1)) (tabT (unpack n w acc)) =
        tabT (unpack n w (wd.foldl (fun a l => pcomp n w (mask w) a (cond l.2 (G l.1) (GI l.1)))
          acc)) ∧
      canonK n w (mask w) (n * w)
        (wd.foldl (fun a l => pcomp n w (mask w) a (cond l.2 (G l.1) (GI l.1))) acc) = true
  | [], acc, ha => ⟨rfl, ha⟩
  | l :: rest, acc, ha => by
    have hl : (if l.2 then g l.1 else gi l.1) = tabT (unpack n w (cond l.2 (G l.1) (GI l.1))) ∧
        canonK n w (mask w) (n * w) (cond l.2 (G l.1) (GI l.1)) = true := by
      cases l.2
      · exact hgi l.1
      · exact hg l.1
    rw [List.foldl_cons, List.foldl_cons, hl.1, compT_unpack ha hl.2]
    exact evalW_foldlG hg hgi rest _ (CFSG.KC.BfsPin.canonK_pcomp ha hl.2)

theorem evalW3_eq {m : Nat} {G GI : Fin m → Nat} {g gi : Fin m → Table}
    (hg : ∀ i, g i = tabT (unpack 3850 12 (G i)) ∧ C3 (G i))
    (hgi : ∀ i, gi i = tabT (unpack 3850 12 (GI i)) ∧ C3 (GI i)) (wd : List (Fin m × Bool)) :
    CFSG.EvenSporadicStandard.TwoHS.evalW 3850 g gi wd = tabT (unpack 3850 12 (EV3 G GI wd)) ∧
      C3 (EV3 G GI wd) := by
  unfold CFSG.EvenSporadicStandard.TwoHS.evalW EV3
  rw [CFSG.KD.HS3850.hid]
  exact evalW_foldlG hg hgi wd _ CFSG.KD.HS3850.hidc

theorem harX_parts (i : Fin 6) : harX i = tabT (unpack 3850 12 (XK i)) ∧ C3 (XK i) :=
  evalW3_eq harA_parts harAI_parts (hsGenWords.getD i.val [])

theorem hpX (i : Fin 6) : invK (XK i) = true := List.all_eq_true.1 hp_x i (List.mem_finRange i)

theorem harXI_parts (i : Fin 6) : harXI i = tabT (unpack 3850 12 (XKI i)) ∧ C3 (XKI i) := by
  refine ⟨?_, (invK_spec (hpX i)).2.1⟩
  unfold harXI
  rw [(harX_parts i).1]
  exact (perm_of (hpX i)).2.1

theorem harPOK_true : harPOK = true := by
  have c1 : (List.finRange 2).all (fun i =>
      permOK 3850 (harA i) && invOK 3850 (harA i) (harAI i)) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [harAI_inv i, harA_eq i, (perm_of (hpA i)).1, (perm_of (hpA i)).2.2]
    rfl
  have c2 : (List.finRange 6).all (fun i =>
      permOK 3850 (harX i) && invOK 3850 (harX i) (harXI i)) = true := by
    rw [List.all_eq_true]
    intro i _
    unfold harXI
    rw [(harX_parts i).1, (perm_of (hpX i)).1, (perm_of (hpX i)).2.2]
    rfl
  have c3 : hsRels.all (fun r => tblEq 3850 (evalW 3850 harX harXI r) (idT 3850)) = true := by
    rw [List.all_eq_true]
    intro r hr
    obtain ⟨e, c⟩ := evalW3_eq harX_parts harXI_parts r
    rw [e, CFSG.KD.HS3850.hid, tblEq_unpack c CFSG.KD.HS3850.hidc]
    exact List.all_eq_true.1 hp_rels r hr
  have c4 : (List.finRange 6).all (fun i =>
      tblEq 3850 (evalW 3850 harX harXI (hsCommWord i)) (harX i)) = true := by
    rw [List.all_eq_true]
    intro i _
    obtain ⟨e, c⟩ := evalW3_eq harX_parts harXI_parts (hsCommWord i)
    rw [e, (harX_parts i).1, tblEq_unpack c (harX_parts i).2]
    exact List.all_eq_true.1 hp_comm i (List.mem_finRange i)
  have hs := hp_surj
  rw [Bool.and_eq_true] at hs
  obtain ⟨ea, ca⟩ := evalW3_eq harX_parts harXI_parts hsSurjA
  obtain ⟨eb, cb⟩ := evalW3_eq harX_parts harXI_parts hsSurjB
  unfold harPOK
  rw [c1, c2, c3, c4, ea, eb, harA_eq 0, harA_eq 1, tblEq_unpack ca (harA_parts 0).2,
    tblEq_unpack cb (harA_parts 1).2, hs.1, hs.2]
  rfl

theorem harXs_getD {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) :
    harXs.getD (l - 1) (idT 3850) = tabT (unpack 3850 12 (LX l)) ∧ C3 (LX l) := by
  have hl : l - 1 < 6 := by omega
  have e : harXs.getD (l - 1) (idT 3850) = harX ⟨l - 1, hl⟩ := by
    simp [harXs, List.getD_eq_getElem?_getD, hl]
  have f : (⟨(l - 1) % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = ⟨l - 1, hl⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hl)
  rw [e]
  unfold LX
  rw [f]
  exact harX_parts _

theorem harUW_letters6 : ∀ j < 3, ∀ l ∈ harUW.getD j [], 1 ≤ l ∧ l ≤ 6 := by decide

theorem wordX_eq {wd : List Nat} (h : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 6) :
    wordTbl 3850 harXs wd = tabT (unpack 3850 12 (wfoldK 3850 12 (mask 12) LX wd idn)) ∧
      C3 (wfoldK 3850 12 (mask 12) LX wd idn) :=
  wordTbl_unpack CFSG.KD.HS3850.hid CFSG.KD.HS3850.hidc fun l hl => harXs_getD (h l hl).1 (h l hl).2

theorem harUX_getD {l : Nat} (h1 : 1 ≤ l) (h3 : l ≤ 3) :
    harUX.getD (l - 1) (idT 3850) = tabT (unpack 3850 12 (UXL l)) ∧ C3 (UXL l) := by
  have hl : l - 1 < 3 := by omega
  have e : harUX.getD (l - 1) (idT 3850) = wordTbl 3850 harXs (harUW.getD (l - 1) []) := by
    rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl <;>
      simp only [harUX, harUW, List.map_cons, List.map_nil, Nat.reduceSub, Nat.sub_self,
        List.getD_cons_zero, List.getD_cons_succ]
  rw [e]
  exact wordX_eq (harUW_letters6 _ hl)

theorem tUX_eq {wd : List Nat} (h : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 3) :
    tUX wd = tabT (unpack 3850 12 (UXK wd)) ∧ C3 (UXK wd) :=
  wordTbl_unpack CFSG.KD.HS3850.hid CFSG.KD.HS3850.hidc fun l hl => harUX_getD (h l hl).1 (h l hl).2

theorem cj_tab {j : Nat} (hj : j < 2) :
    harConj j = tabT (unpack 3850 12 (CJ.F j)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound CJ.all (by norm_num) j hj
  rw [← CJ.eq] at h
  unfold harConj
  rw [← h, tabT_natArr]

theorem conjOK_word {C r x : Nat}
    {w : List Nat} (hw : ∀ l ∈ w, l < 16) (he : Nat.beq C (wfoldR CFSG.KD.LQT.HN.ls8 w) = true)
    (hi : invK C = true) (hr : C3 r) (h : conjK C r x = true) :
    conjOK 3850 hsSift (tabT (unpack 3850 12 C)) (tabT (unpack 3850 12 r))
      (tabT (unpack 3850 12 x)) = true := by
  obtain ⟨c, ci, -⟩ := invK_spec hi
  obtain ⟨p1, e, p2⟩ := perm_of hi
  have hs : hsSift (tabT (unpack 3850 12 C)) = true := by
    obtain ⟨g, hg, hrep⟩ := CFSG.KD.LQT.HN.rep_word _ hw
    rw [← Nat.eq_of_beq_eq_true he] at hrep
    refine (CFSG.KD.LQT.HN.sift_iff (G := g) ?_).2 hg
    rw [natArr_tabT c]
    exact hrep
  have hx : C3 x := by
    rw [← Nat.eq_of_beq_eq_true h]
    exact CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp c hr) ci
  unfold conjOK conjT
  rw [p1, p2, hs, e, compT_unpack c hr, compT_unpack (CFSG.KC.BfsPin.canonK_pcomp c hr) ci,
    tblEq_unpack (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp c hr) ci) hx]
  exact h

theorem harLiftOK_true :
    harLiftOK = true := by
  have hu := hl_u
  simp only [Bool.and_eq_true] at hu
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := hu
  have hx := hl_x
  simp only [Bool.and_eq_true] at hx
  obtain ⟨⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩, hx5⟩ := hx
  have hw3 : ∀ w ∈ harUW, ∃ j < 3, harUW.getD j [] = w := by
    intro w hw
    simp only [harUW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  have l1 : harU.all (permOK 11200) = true := by
    rw [List.all_eq_true]
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    obtain ⟨j, hj3, rfl⟩ := hw3 w hw
    exact (word_inv (harUW_letters j hj3)
      (List.all_eq_true.1 hu1 j (List.mem_range.2 hj3))).2.2.2.2.1
  have l2 : harUX.all (permOK 3850) = true := by
    rw [List.all_eq_true]
    intro u hu
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
    obtain ⟨j, hj3, rfl⟩ := hw3 w hw
    have hi : invK (UXL (j + 1)) = true := List.all_eq_true.1 hx1 j (List.mem_range.2 hj3)
    rw [(wordX_eq (harUW_letters6 j hj3)).1]
    exact (perm_of hi).1
  have hcj := fun j (hj : j < 2) => (bAnd_iff _ _).1 (List.all_eq_true.1 hx3 j (List.mem_range.2 hj))
  have hcw : ∀ j < 2, ∀ l ∈ cjW.getD j [], l < 16 := by decide
  obtain ⟨e0, c0⟩ := tU_eq (wd := [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) (by decide)
  obtain ⟨e5, c5⟩ := tU_eq (wd := [1, 2, 1, 2, 3]) (by decide)
  obtain ⟨f4, d4⟩ := tUX_eq (wd := [3, 3, 3, 3]) (by decide)
  obtain ⟨f5, d5⟩ := tUX_eq (wd := [1, 2, 1, 2, 3]) (by decide)
  obtain ⟨f10, d10⟩ := tUX_eq (wd := [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) (by decide)
  have k1 := conjOK_word (hcw 0 (by norm_num)) (hcj 0 (by norm_num)).1 (hcj 0 (by norm_num)).2
    (CFSG.KD.HS3850.cent_cn (k := 5) (by norm_num)) hx4
  have k2 := conjOK_word (hcw 1 (by norm_num)) (hcj 1 (by norm_num)).1 (hcj 1 (by norm_num)).2
    (CFSG.KD.HS3850.cent_cn (k := 12) (by norm_num)) hx5
  unfold harLiftOK harC0
  rw [l1, l2, e0, e5, f4, f5, f10, idT_eq, CFSG.KD.HS3850.hid, cj_tab (by norm_num), cj_tab (by norm_num),
    CFSG.KD.HS3850.cent_tab (k := 5) (by norm_num), CFSG.KD.HS3850.cent_tab (k := 12) (by norm_num),
    k1, k2, tblEq_unpack c0 cId, comp_eq c5 c5, tblEq_unpack (cPc c5 c5) c0,
    tblEq_unpack d10 CFSG.KD.HS3850.hidc]
  simp only [Bool.not_eq_true'] at hu2
  have hx2' : Nat.beq (UXK [1, 2, 1, 2, 3, 1, 2, 1, 2, 3]) (pidn 3850 12) = true := hx2
  rw [hu2, hu3, hx2']
  rfl

theorem har_true :
    harModelOK = true ∧ harPOK = true ∧ harLiftOK = true :=
  ⟨harModelOK_true, harPOK_true, harLiftOK_true⟩

end CFSG.KD.TwoHS

end

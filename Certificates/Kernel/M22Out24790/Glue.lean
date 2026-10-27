module

public import Certificates.Kernel.M22Out24790.Checks
public import CFSG.Certificates.Kernel.M22Out.CensusSound
import all CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutTab47Check

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelM22Out24790

open CFSG.KC.M22Out CFSG.KD.M22Out24790
open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.FusionCheck
  CFSG.EvenSporadicStandard.M22Std.OutCheck

private theorem gD {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem gD_mem {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d ∈ l := by
  rw [gD h]
  exact List.getElem_mem h

private theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

private theorem validT_iff (t : Tab) : validT t = true ↔ ValidT t := by
  unfold validT ValidT
  simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true, Nat.blt_eq]

private theorem all_valid {L : List Tab} (h : L.all validT = true) : ∀ t ∈ L, ValidT t :=
  fun t ht => (validT_iff t).1 (List.all_eq_true.1 h t ht)

private theorem sm1 : nGensTab.all validT = true := by decide +kernel
private theorem sm2 : nGensTab.length = 2 := by decide +kernel
private theorem sm3 : ((List.range 3).all fun i => validT (gens3.getD i idTab) &&
    validT (GI.getD i idTab) && tmul (GI.getD i idTab) (gens3.getD i idTab) == idTab &&
    tmul (gens3.getD i idTab) (GI.getD i idTab) == idTab) = true := by decide +kernel
private theorem sm4 : GI.getD 2 idTab = betaTab := by decide +kernel
private theorem sm5 : validT betaTab = true := by decide +kernel
private theorem sm6 : tmul betaTab betaTab = idTab := by decide +kernel
private theorem sm7 : (PR.all fun e => Nat.blt e.1 375) = true := by decide +kernel
private theorem sm9 : ((List.range 12).all fun s => Nat.ble (IC.getD s 0) (IC.getD (s + 1) 0)) =
    true := by decide +kernel
private theorem sm10 : ∀ i < 2, gens3.getD i idTab = nGensTab.getD i idTab := by decide +kernel
private theorem sm11 : gens3.getD 2 idTab = betaTab := by decide +kernel

private theorem census0 :
    (decide ((CL.map fun c => invClassData.getD c (0, 0, false, false)).length = 375) &&
      decide (((CL.map fun c => invClassData.getD c (0, 0, false, false)).filter
        (·.2.2.1)).length = 195) &&
      (CL.map fun c => invClassData.getD c (0, 0, false, false)).all
        (fun d => decide (d ∈ invClassData)) &&
      classTable.all fun e =>
        classCount (CL.map fun c => invClassData.getD c (0, 0, false, false)) e.1 e.2.1 ==
          e.2.2) = true := by
  decide +kernel

private theorem letter {l : Nat} (hl : l < 3) :
    ValidT (gens3.getD l idTab) ∧ ValidT (GI.getD l idTab) ∧
      tmul (GI.getD l idTab) (gens3.getD l idTab) = idTab ∧
      tmul (gens3.getD l idTab) (GI.getD l idTab) = idTab := by
  have := List.all_eq_true.1 sm3 l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨(validT_iff _).1 this.1.1.1, (validT_iff _).1 this.1.1.2, this.1.2, this.2⟩

private theorem head :
    T.headD [] = idTab ∧ W.headD [0] = [] ∧ T.length = 5760 ∧ W.length = 5760 ∧
      U.length = 5760 ∧ cs.getD 0 0 = 1 ∧ cs.getD 12 0 = 5760 ∧
      ∀ w ∈ W, w.length < 17 ∧ ∀ i ∈ w, i < 2 := by
  have h := ch24790head
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩, h7⟩, h8⟩, -⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h6, h7, h8, h10⟩

private theorem valid :
    (∀ t ∈ T, ValidT t) ∧ (∀ t ∈ U, ValidT t) ∧ ∀ t ∈ IT, ValidT t := by
  have h := ch24790valid
  simp only [Bool.and_eq_true] at h
  exact ⟨all_valid h.1.1, all_valid h.1.2, all_valid h.2⟩

private theorem icf : IC.getD 0 0 = 0 ∧ IC.getD 12 0 = 375 ∧ IT.length = 375 ∧ IX.length = 375 := by
  have h := ch24790ic
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩

private theorem treef : conjTreeK gens3 GI IT PR PR IT = true ∧ PR.length = 375 ∧
    CL.length = 375 ∧ classTreeOK = true := by
  have h := ch24790tree
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

private theorem normf : tmul (tmul betaTab (nGensTab.getD 0 idTab)) betaTab ∈ T ∧
    tmul (tmul betaTab (nGensTab.getD 1 idTab)) betaTab ∈ T ∧
    (nGensTab.all fun g => normOK (elemTabs 1) g) = true := by
  have h := ch24790norm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.2⟩

private theorem hseg : ∀ s < 12, segOK s = true := fun s hs =>
  match s, hs with
  | 0, _ => ch24790seg0
  | 1, _ => ch24790seg1
  | 2, _ => ch24790seg2
  | 3, _ => ch24790seg3
  | 4, _ => ch24790seg4
  | 5, _ => ch24790seg5
  | 6, _ => ch24790seg6
  | 7, _ => ch24790seg7
  | 8, _ => ch24790seg8
  | 9, _ => ch24790seg9
  | 10, _ => ch24790seg10
  | 11, _ => ch24790seg11
  | n + 12, h => absurd h (by omega)

private noncomputable def RS (s : Nat) : Nat :=
  replayK TP WP (nGensTab.getD 0 idTab) (nGensTab.getD 1 idTab) (T.drop (480 * s))
    (EW.drop (480 * s)) (KK.drop (480 * s)) (480 * s) (cs.getD s 0)

private theorem RS_succ {s : Nat} (hs : s < 12) : RS s = RS (s + 1) := by
  have hT := head.2.2.1
  have hl : ((T.drop (480 * s)).take 480).length = 480 := by
    rw [List.length_take, List.length_drop, hT]
    omega
  have e := List.take_append_drop 480 (T.drop (480 * s))
  have hk := hseg s hs
  unfold segOK at hk
  unfold RS
  conv => lhs; rw [← e]
  rw [replayK_append, hl, List.drop_drop, List.drop_drop, List.drop_drop,
    Nat.eq_of_beq_eq_true hk, show 480 * s + 480 = 480 * (s + 1) by omega]

private theorem RS_chain : ∀ m, m ≤ 12 → RS 0 = RS m
  | 0, _ => rfl
  | m + 1, h => (RS_chain m (by omega)).trans (RS_succ (by omega))

private theorem replay_full : replayK (packTs T) (packW W) (nGensTab.getD 0 idTab)
    (nGensTab.getD 1 idTab) T (W.map encW) KK 0 1 = T.length := by
  have h12 := RS_chain 12 (Nat.le_refl 12)
  obtain ⟨-, -, hT, -, -, hc0, hc12, -⟩ := head
  unfold RS at h12
  rw [Nat.mul_zero, List.drop_zero, List.drop_zero, List.drop_zero, hc0,
    show 480 * 12 = T.length by omega, List.drop_length, hc12] at h12
  rw [hT]
  exact h12

private theorem hu : ∀ s < 6, uSegOK s = true := fun s hs =>
  match s, hs with
  | 0, _ => ch24790u0
  | 1, _ => ch24790u1
  | 2, _ => ch24790u2
  | 3, _ => ch24790u3
  | 4, _ => ch24790u4
  | 5, _ => ch24790u5
  | n + 6, h => absurd h (by omega)

private theorem U_eq : T.map (tmul betaTab) = U := by
  obtain ⟨-, -, hT, -, hU, -, -, -⟩ := head
  obtain ⟨hvT, hvU, -⟩ := valid
  have hb : ValidT betaTab := (validT_iff _).1 sm5
  have step : ∀ m, m ≤ 6 →
      (T.drop (960 * (6 - m))).map (tmul betaTab) = U.drop (960 * (6 - m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, show 960 * 6 = T.length by omega, List.drop_length,
        show T.length = U.length by omega, List.drop_length]
      rfl
    | succ m ih =>
      intro hm
      have hs := hu (5 - m) (by omega)
      unfold uSegOK at hs
      have hc := map_eq_of_mapEqK _ _ (by simp [List.length_take, List.length_drop, hT, hU])
        (fun a ha => tmul_valid hb (hvT a (List.mem_of_mem_drop (List.mem_of_mem_take ha))))
        (fun b hb' => hvU b (List.mem_of_mem_drop (List.mem_of_mem_take hb'))) hs
      have e1 := List.take_append_drop 960 (T.drop (960 * (5 - m)))
      have e2 := List.take_append_drop 960 (U.drop (960 * (5 - m)))
      rw [List.drop_drop, show 960 * (5 - m) + 960 = 960 * (6 - m) by omega] at e1 e2
      rw [show 6 - (m + 1) = 5 - m by omega, ← e1, ← e2, List.map_append, hc, ih (by omega)]
  have := step 6 (Nat.le_refl 6)
  rwa [Nat.sub_self, Nat.mul_zero, List.drop_zero, List.drop_zero] at this

private theorem nodupTU : ((T ++ U).map keyOf).Nodup := by
  have h := ch24790keys
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨-, -, hT, -, hU, -, -, -⟩ := head
  obtain ⟨hvT, hvU, -⟩ := valid
  exact keys_nodup h.1 h.2 (by simp [hT, hU])
    (fun t ht => (List.mem_append.1 ht).elim (hvT t) (hvU t))

private theorem nodupL : (T ++ U).Nodup := List.Nodup.of_map keyOf nodupTU

private theorem nodupT : (T.map keyOf).Nodup := by
  have := nodupTU
  rw [List.map_append, List.nodup_append] at this
  exact this.1

private theorem headD_getD {α : Type} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

private theorem bfs : bfsWords nGensTab = W ∧ W.map (wordTab nGensTab) = T := by
  obtain ⟨hT0, hW0, hT, hWl, -, -, -, hW⟩ := head
  have hW0' : W.getD 0 [] = [] := by
    have hpos : 0 < W.length := by omega
    rw [gD hpos]
    rw [headD_getD, gD hpos] at hW0
    exact hW0
  exact bfsWords_eq_of_replay sm2 (all_valid sm1) valid.1 (List.Nodup.of_map keyOf nodupT)
    (by rw [← headD_getD]; exact hT0) hW0' (by rw [hT, hWl]) hW replay_full

private theorem tabLI_eq : tabLI = T := by
  have e : innerWords = bfsWords nGensTab := rfl
  unfold tabLI
  rw [e, bfs.1, bfs.2]

private theorem tabL_eq : tabL = T ++ U := by
  unfold tabL
  rw [tabLI_eq, U_eq]

private theorem hyp : ClosedHyp nGensTab GI T betaTab := by
  obtain ⟨hT0, -, hT, hWl, -, -, -, hW⟩ := head
  have hnd : T.Nodup := List.Nodup.of_map keyOf nodupT
  refine ⟨valid.1, hnd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (validT_iff _).1 sm5, sm6, ?_⟩
  · rw [headD_getD] at hT0
    rw [← hT0]
    exact gD_mem (by omega)
  · exact mul_mem_of_replay sm2 (all_valid sm1) valid.1 hnd (by rw [hT, hWl]) hW replay_full
  · intro t ht
    rw [← bfs.2] at ht
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 ht
    exact ⟨w, (hW w hw).2, rfl⟩
  · intro i hi
    have := (letter (l := i) (by omega)).1
    rwa [sm10 i hi] at this
  · intro i hi
    exact (letter (l := i) (by omega)).2.1
  · intro i hi
    have := (letter (l := i) (by omega)).2.2.1
    rwa [sm10 i hi] at this
  · intro i hi
    have := (letter (l := i) (by omega)).2.2.2
    rwa [sm10 i hi] at this
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact normf.1
    · exact normf.2.1

private theorem hcl {l : Nat} (hl : l < 3) :
    ∀ x ∈ T ++ U, tmul (tmul (GI.getD l idTab) x) (gens3.getD l idTab) ∈ T ++ U := by
  intro x hx
  rw [← U_eq] at hx ⊢
  rcases (by omega : l < 2 ∨ l = 2) with h | h
  · rw [sm10 l h]
    exact hyp.conj_gen h hx
  · subst h
    rw [sm11, sm4]
    exact hyp.conj_beta hx

private theorem hvL : ∀ t ∈ T ++ U, ValidT t :=
  fun t ht => (List.mem_append.1 ht).elim (valid.1 t) (valid.2.1 t)

private theorem hvIT {j : Nat} (hj : j < 375) : ValidT (IT.getD j idTab) :=
  valid.2.2 _ (gD_mem (by rw [icf.2.2.1]; exact hj))

private theorem rep {j : Nat} (hj : j < 375) (h3 : (PR[j]'(by rw [treef.2.1]; exact hj)).2.1 = 3) :
    centN (T ++ U) (IT.getD j idTab) = centOf (CL.getD j 5) := by
  have h := ch24790repIdx
  have hlen : j < (PR.zip (List.range 375)).length := by simp [treef.2.1, hj]
  have := List.all_eq_true.1 h _ (List.getElem_mem hlen)
  simp only [List.getElem_zip, List.getElem_range, h3, Nat.beq_refl, Bool.not_true,
    Bool.false_or] at this
  have hm : j ∈ repIdx := List.contains_iff_mem.1 this
  simp only [repIdx, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · have := ch24790rep0
    unfold repOK at this
    exact Nat.eq_of_beq_eq_true this
  · have := ch24790rep12
    unfold repOK at this
    exact Nat.eq_of_beq_eq_true this
  · have := ch24790rep195
    unfold repOK at this
    exact Nat.eq_of_beq_eq_true this
  · have := ch24790rep196
    unfold repOK at this
    exact Nat.eq_of_beq_eq_true this
  · have := ch24790rep197
    unfold repOK at this
    exact Nat.eq_of_beq_eq_true this

private theorem cent_all : ∀ d j (hj : j < 375),
    (PR[j]'(by rw [treef.2.1]; exact hj)).2.2 ≤ d →
      centN (T ++ U) (IT.getD j idTab) = centOf (CL.getD j 5) := by
  have hPR := treef.2.1
  have hclass : ∀ j (hj : j < 375),
      CL.getD (PR[j]'(by rw [hPR]; exact hj)).1 5 = CL.getD j 5 := by
    intro j hj
    have h := treef.2.2.2
    unfold classTreeOK at h
    have hlen : j < (PR.zip CL).length := by simp [hPR, treef.2.2.1, hj]
    have := List.all_eq_true.1 h _ (List.getElem_mem hlen)
    simp only [List.getElem_zip, Nat.beq_eq] at this
    rw [this, gD (by rw [treef.2.2.1]; exact hj)]
  have hpar : ∀ j (hj : j < 375), (PR[j]'(by rw [hPR]; exact hj)).1 < 375 := by
    intro j hj
    have := List.all_eq_true.1 sm7 _ (List.getElem_mem (by rw [hPR]; exact hj))
    simpa only [Nat.blt_eq] using this
  intro d
  induction d with
  | zero =>
    intro j hj hd
    rcases conjTreeK_spec gens3 GI IT PR PR IT treef.1 j (by rw [hPR]; exact hj) with
      ⟨h3, -⟩ | ⟨-, hdep, -⟩
    · exact rep hj h3
    · omega
  | succ d ih =>
    intro j hj hd
    rcases conjTreeK_spec gens3 GI IT PR PR IT treef.1 j (by rw [hPR]; exact hj) with
      ⟨h3, -⟩ | ⟨hl, hdep, hconj⟩
    · exact rep hj h3
    · have hp := hpar j hj
      obtain ⟨hg, hgi, h1, h2⟩ := letter hl
      rw [← hconj, centN_conj hg hgi h1 h2 nodupL hvL (hcl hl) (hvIT hp)]
      rw [gD (l := PR) (d := (0, 0, 0)) (by omega)] at hdep
      rw [ih _ hp (by omega), hclass j hj]

private theorem hi : ∀ s < 12, invSegOK s = true := fun s hs =>
  match s, hs with
  | 0, _ => ch24790i0
  | 1, _ => ch24790i1
  | 2, _ => ch24790i2
  | 3, _ => ch24790i3
  | 4, _ => ch24790i4
  | 5, _ => ch24790i5
  | 6, _ => ch24790i6
  | 7, _ => ch24790i7
  | 8, _ => ch24790i8
  | 9, _ => ch24790i9
  | 10, _ => ch24790i10
  | 11, _ => ch24790i11
  | n + 12, h => absurd h (by omega)

private theorem filter_eq : (T ++ U).filter isInv = IT := by
  obtain ⟨-, -, hT, -, hU, -, -, -⟩ := head
  have hL : (T ++ U).length = 11520 := by simp [hT, hU]
  obtain ⟨hIC0, hIC12, hIT, -⟩ := icf
  have step : ∀ m, m ≤ 12 →
      ((T ++ U).drop (960 * (12 - m))).filter isInv = IT.drop (IC.getD (12 - m) 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero, hIC12, show 960 * 12 = (T ++ U).length by omega, List.drop_length,
        show (375 : Nat) = IT.length by omega, List.drop_length]
      rfl
    | succ m ih =>
      intro hm
      have hs := hi (11 - m) (by omega)
      unfold invSegOK at hs
      have hc := eq_of_map_packT _ _
        (fun a ha => hvL a (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_filter ha))))
        (fun b hb => valid.2.2 b (List.mem_of_mem_drop (List.mem_of_mem_take hb)))
        (beq_iff_eq.1 hs)
      have e1 := List.take_append_drop 960 ((T ++ U).drop (960 * (11 - m)))
      rw [List.drop_drop, show 960 * (11 - m) + 960 = 960 * (12 - m) by omega] at e1
      have hmn : IC.getD (11 - m) 0 ≤ IC.getD (11 - m + 1) 0 := by
        have := List.all_eq_true.1 sm9 (11 - m) (List.mem_range.2 (by omega))
        simpa only [Nat.ble_eq] using this
      have e2 := List.take_append_drop (IC.getD (11 - m + 1) 0 - IC.getD (11 - m) 0)
        (IT.drop (IC.getD (11 - m) 0))
      rw [List.drop_drop, Nat.add_sub_of_le hmn] at e2
      rw [show 12 - (m + 1) = 11 - m by omega, ← e1, List.filter_append, hc, ih (by omega),
        show 12 - m = 11 - m + 1 by omega]
      exact e2
  have := step 12 (Nat.le_refl 12)
  rwa [Nat.sub_self, Nat.mul_zero, List.drop_zero, hIC0, List.drop_zero] at this

private theorem data_j {j : Nat} (hj : j < 375) :
    packT (IT.getD j idTab) = tabAt LP (IX.getD j 0) ∧ IX.getD j 0 < 11520 ∧
      Nat.blt (IX.getD j 0) 5760 = (invClassData.getD (CL.getD j 5) (0, 0, false, false)).2.2.1 ∧
      fixF (IT.getD j idTab) = (invClassData.getD (CL.getD j 5) (0, 0, false, false)).2.1 ∧
      decide (IT.getD j idTab ∈ f1Tabs) =
        (invClassData.getD (CL.getD j 5) (0, 0, false, false)).2.2.2 := by
  have h := ch24790data
  unfold dataOK at h
  obtain ⟨-, -, hIT, hIX⟩ := icf
  have hCL := treef.2.2.1
  have hlen : j < (IT.zip (IX.zip CL)).length := by simp [hIT, hIX, hCL, hj]
  have := List.all_eq_true.1 h _ (List.getElem_mem hlen)
  simp only [List.getElem_zip, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, beq_iff_eq] at this
  rw [gD (l := IT) (by rw [hIT]; exact hj), gD (l := IX) (by rw [hIX]; exact hj),
    gD (l := CL) (by rw [hCL]; exact hj)]
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩

private theorem memT {j : Nat} (hj : j < 375) :
    decide (IT.getD j idTab ∈ T) = Nat.blt (IX.getD j 0) 5760 := by
  obtain ⟨hp, hlt, -, -, -⟩ := data_j hj
  obtain ⟨-, -, hT, -, hU, -, -, -⟩ := head
  have hL : (T ++ U).length = 11520 := by simp [hT, hU]
  have hk : IX.getD j 0 < (T ++ U).length := by omega
  have hp' : packT (IT.getD j idTab) = tabAt (packTs (T ++ U)) (IX.getD j 0) := hp
  rw [tabAt_packTs hvL hk] at hp'
  have he := packT_inj (hvIT hj) (hvL _ (List.getElem_mem hk)) hp'
  rw [blt_dec, decide_eq_decide]
  constructor
  · intro hmem
    by_contra hx
    have hUm : IT.getD j idTab ∈ U := by
      rw [he, List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    exact (List.nodup_append.1 nodupL).2.2 _ hmem _ hUm rfl
  · intro hx
    rw [he, List.getElem_append_left (by omega)]
    exact List.getElem_mem _

private theorem data_eq :
    IT.map (invData (T ++ U) T) = CL.map fun c => invClassData.getD c (0, 0, false, false) := by
  obtain ⟨-, -, hIT, -⟩ := icf
  have hCL := treef.2.2.1
  apply List.ext_getElem
  · simp [hIT, hCL]
  · intro j h1 h2
    have hj : j < 375 := by simpa [hIT] using h1
    rw [List.getElem_map, List.getElem_map, ← gD (d := idTab) (by rw [hIT]; exact hj),
      ← gD (d := 5) (by rw [hCL]; exact hj)]
    obtain ⟨-, -, hin, hfix, hf1⟩ := data_j hj
    unfold invData
    rw [cent_all _ j hj (Nat.le_refl _), hfix, memT hj, hin, hf1]
    rfl

private theorem censusOK_of {L LI IT' : List Tab} {D0 : List (Nat × Nat × Bool × Bool)}
    (h1 : L.filter isInv = IT') (h2 : IT'.map (invData L LI) = D0)
    (h3 : (decide (D0.length = 375) && decide ((D0.filter (·.2.2.1)).length = 195) &&
      D0.all (fun d => decide (d ∈ invClassData)) &&
      classTable.all fun e => classCount D0 e.1 e.2.1 == e.2.2) = true) :
    censusOK L LI = true := by
  have hlen : IT'.length = D0.length := by rw [← h2, List.length_map]
  have hf : (IT'.filter fun t => decide (t ∈ LI)).length = (D0.filter (·.2.2.1)).length := by
    rw [← h2, List.filter_map, List.length_map]
    rfl
  unfold censusOK
  simp only [h1]
  rw [h2, hlen, hf]
  exact h3

theorem censusCheck_true : censusCheck = true := by
  obtain ⟨-, -, hT, -, hU, -, -, -⟩ := head
  unfold censusCheck
  rw [tabL_eq, tabLI_eq]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨normf.2.2, hT⟩, nodupCheck_of_nodup nodupT⟩, by simp [hT, hU]⟩,
    nodupCheck_of_nodup nodupTU⟩, censusOK_of filter_eq data_eq census0⟩

end CertificateChecks.KernelM22Out24790

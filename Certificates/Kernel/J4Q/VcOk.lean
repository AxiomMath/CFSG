module

public import Certificates.Kernel.J4Q.VcK
public import Certificates.Kernel.J4Q.VlOk
public import Certificates.Kernel.J4Q.X0OrbOk
public import Certificates.Kernel.J4Q.D2B3
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem inLK_eq (x : Nat) : ∀ l : List Nat, inLK x l = l.any (Nat.beq x)
  | [] => rfl
  | y :: l => by
    change orB (Nat.beq x y) (inLK x l) = _
    rw [orB_eq'', inLK_eq x l, List.any_cons]

theorem beq_comm' (a b : Nat) : Nat.beq a b = Nat.beq b a := by
  apply Bool.eq_iff_iff.2
  rw [Nat.beq_eq, Nat.beq_eq]
  exact eq_comm

theorem inLK_mem' {x : Nat} {l : List Nat} (h : inLK x l = true) : x ∈ l := by
  rw [inLK_eq, List.any_eq_true] at h
  obtain ⟨y, hy, e⟩ := h
  rw [Nat.eq_of_beq_eq_true e]
  exact hy

theorem allAny_enc {A B : List (Array V2)} (hA : ∀ X ∈ A, WfA X) (hB : ∀ X ∈ B, WfA X) :
    (A.all fun X => B.any (eqRows X)) = allLK (fun x => inLK x (B.map encR)) (A.map encR) := by
  rw [allLK_eq, List.all_map]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, Function.comp_apply]
  refine forall₂_congr fun X hX => ?_
  rw [any_grp ⟨hA X hX, rfl⟩ hB, inLK_eq]

theorem allAny_enc' {A B : List (Array V2)} (hA : ∀ X ∈ A, WfA X) (hB : ∀ X ∈ B, WfA X) :
    (A.all fun X => B.any fun Y => eqRows Y X) = allLK (fun x => inLK x (B.map encR)) (A.map encR) := by
  rw [← allAny_enc hA hB]
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  refine forall₂_congr fun X hX => ?_
  simp only [List.any_eq_true]
  refine exists_congr fun Y => and_congr_right fun hY => ?_
  rw [eqRows_of ⟨hB Y hY, rfl⟩ ⟨hA X hX, rfl⟩, eqRows_of ⟨hA X hX, rfl⟩ ⟨hB Y hY, rfl⟩, beq_comm']

theorem vlCx_size : vlCx.size = 6720 := by
  have h := congrArg List.length x0Orb_ok.2.1
  rw [List.length_map, List.length_map, List.length_range, Array.length_toList] at h
  exact h

theorem cx_enc {k : Nat} (hk : k < 6720) :
    WfA vlCx[k]! ∧ encR vlCx[k]! = CFSG.KD.X0O.MSF k := by
  obtain ⟨-, hm, hw⟩ := x0Orb_ok
  have hs : k < x0Orb.mats.toList.length := by
    rw [Array.length_toList]
    exact vlCx_size ▸ hk
  have e : vlCx[k]! = x0Orb.mats.toList[k] := by
    unfold vlCx
    rw [getElem!_pos x0Orb.mats k (by simpa using hs), Array.getElem_toList]
  rw [e]
  refine ⟨hw _ (List.getElem_mem _), ?_⟩
  have := congrArg (fun l => l[k]?) hm
  simp only [List.getElem?_map, List.getElem?_range hk, List.getElem?_eq_getElem hs,
    Option.map_some, Option.some.injEq] at this
  exact this

theorem cxi_enc {k ci : Nat} (hk : k < 6720) (hcan : canonJ pad (CFSG.KD.X0O.MSF ci) = true)
    (hm : Nat.beq (mulJ c rm (CFSG.KD.X0O.MSF k) (CFSG.KD.X0O.MSF ci)) one = true) :
    WfA vlCxInv[k]! ∧ encR vlCxInv[k]! = CFSG.KD.X0O.MSF ci := by
  have e : vlCxInv[k]! = invRows vlCx[k]! := by
    unfold vlCxInv
    rw [getElem!_pos _ k (by simp [vlCx_size, hk]), Array.getElem_map,
      getElem!_pos vlCx k (by simp [vlCx_size, hk])]
  rw [e]
  exact invRows_enc hK (cx_enc hk).1 hcan (by rw [(cx_enc hk).2]; exact hm)

@[expose] def VlK4011 : Prop :=
  (∀ j < 75, vlJK j = true) ∧ (∀ t < 32, etaCK t = true) ∧ (∀ t < 256, segK t = true) ∧
    ∀ p < 1980, pairAtK p = true

theorem vlGroups_inv (h : VlK4011) : GInv 1980 vlGroups := groups_inv h.1 h.2.1 h.2.2.1 h.2.2.2

theorem vlGroups_inv' (h : VlK4011) : vlGroups.length = getN 0 VLC 1980 ∧
    ∀ g < getN 0 VLC 1980, (∀ M ∈ vlGroups.getD g [], WfA M) ∧ (vlGroups.getD g []).map encR = grpK g :=
  vlGroups_inv h

theorem vlGroups_len (h : VlK4011) : vlGroups.length = 132 := (vlGroups_inv' h).1.trans vlc1980

theorem lines17_len : lines17.length = 17 := by
  rw [lines17_eq]
  simp [L17]

theorem vlAll_size' (h : VlK4011) : vlAll.size = 149 := by
  unfold vlAll
  simp [lines17_len, vlGroups_len h]

theorem il17_lt (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true) {i : Nat}
    (hi : i < 272) : getN 0 IL17 i < 2048 := lt_of_blt (allR_spec hl i hi)

theorem vlAll_toList : vlAll.toList =
    (lines17.map fun S => (S.map etaE).toArray) ++ vlGroups.map List.toArray := rfl

theorem vlAll_getD {g : Nat} (hs : g < vlAll.size) : vlAll[g]! = (vlAll.toList[g]?).getD #[] := by
  rw [getElem!_pos vlAll g hs, List.getElem?_eq_getElem (by simpa using hs), Option.getD_some,
    Array.getElem_toList]

theorem vlAll_lo {g : Nat} (hg : g < 17) :
    vlAll[g]!.toList = ((List.range 16).map fun j => getN 0 IL17 (16 * g + j)).map etaE := by
  have hl : g < lines17.length := by rw [lines17_len]; exact hg
  have hs : g < vlAll.size := by unfold vlAll; simp; omega
  rw [vlAll_getD hs, vlAll_toList, List.getElem?_append_left (by simpa using hl), List.getElem?_map,
    lines17_eq, L17, List.getElem?_map, List.getElem?_range hg]
  rfl

theorem vlAll_hi (h : VlK4011) {g : Nat} (hg : 17 ≤ g) (hg' : g < 149) :
    vlAll[g]!.toList = vlGroups.getD (g - 17) [] := by
  have hs : g < vlAll.size := by rw [vlAll_size' h]; exact hg'
  have hlen : (lines17.map fun S => (S.map etaE).toArray).length = 17 := by
    rw [List.length_map, lines17_len]
  have hg2 : g - 17 < vlGroups.length := by rw [vlGroups_len h]; omega
  rw [vlAll_getD hs, vlAll_toList, List.getElem?_append_right (by omega), hlen, List.getElem?_map,
    List.getElem?_eq_getElem hg2, Option.map_some, Option.getD_some, List.getD_eq_getElem _ _ hg2]

theorem vlAll_enc (h : VlK4011) (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true)
    {g : Nat} (hg : g < 149) :
    (∀ M ∈ vlAll[g]!.toList, WfA M) ∧ vlAll[g]!.toList.map encR = gaK g := by
  by_cases hlo : g < 17
  · have hb : Nat.blt g 17 = true := Nat.ble_eq_true_of_le hlo
    have hm : ∀ j < 16, getN 0 IL17 (16 * g + j) < 2048 := fun j hj => il17_lt hl (by omega)
    rw [vlAll_lo hlo]
    refine ⟨fun M hM => ?_, ?_⟩
    · obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hM
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hm'
      exact (ef_enc h.2.1 (hm j (List.mem_range.1 hj))).1
    · unfold gaK
      rw [hb]
      change _ = smapK _ (rangeK 16)
      rw [smapK_eq, rangeK_eq, List.map_map, List.map_map]
      refine List.map_congr_left fun j hj => ?_
      rw [Function.comp_apply, Function.comp_apply, (ef_enc h.2.1 (hm j (List.mem_range.1 hj))).2]
      rfl
  · have hb : Nat.blt g 17 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact hlo (Nat.le_of_ble_eq_true e)
    have hI := (vlGroups_inv' h).2 (g - 17) (by rw [vlc1980]; omega)
    rw [vlAll_hi h (by omega) hg]
    refine ⟨hI.1, ?_⟩
    unfold gaK
    rw [hb]
    exact hI.2

theorem conjEq_eq (h : VlK4011) (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true)
    {r g cc ci : Nat} (hr : r < 149) (hg : g < 149) (hcc : cc < 6720)
    (hcan : canonJ pad (CFSG.KD.X0O.MSF ci) = true)
    (hm : Nat.beq (mulJ c rm (CFSG.KD.X0O.MSF cc) (CFSG.KD.X0O.MSF ci)) one = true) :
    vlConjEq r g cc =
      sameK (conjLK (CFSG.KD.X0O.MSF cc) (CFSG.KD.X0O.MSF ci) (gaK r)) (gaK g) := by
  obtain ⟨hwr, her⟩ := vlAll_enc h hl hr
  obtain ⟨hwg, heg⟩ := vlAll_enc h hl hg
  have hx := cx_enc hcc
  have hxi := cxi_enc hcc hcan hm
  have hcj : ∀ M ∈ vlAll[r]!.toList, WfA (vlConjBy cc M) ∧
      encR (vlConjBy cc M) = mulJ c rm (mulJ c rm (CFSG.KD.X0O.MSF cc) (encR M)) (CFSG.KD.X0O.MSF ci) :=
    fun M hM => mul_enc hK (mul_enc hK hx ⟨hwr M hM, rfl⟩) hxi
  have hwc : ∀ X ∈ vlAll[r]!.toList.map (vlConjBy cc), WfA X := by
    intro X hX
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hX
    exact (hcj M hM).1
  have hec : (vlAll[r]!.toList.map (vlConjBy cc)).map encR =
      conjLK (CFSG.KD.X0O.MSF cc) (CFSG.KD.X0O.MSF ci) (gaK r) := by
    rw [conjLK, smapK_eq, ← her, List.map_map, List.map_map]
    exact List.map_congr_left fun M hM => (hcj M hM).2
  unfold vlConjEq sameK
  simp only [← Array.all_toList, ← Array.any_toList, Array.toList_map]
  rw [allAny_enc hwc hwg, allAny_enc' hwg hwc, hec, heg, andB_eq]

theorem cls_of (h : VlK4011) (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true)
    (hv : ∀ g < 149, vcK g = true) {g : Nat} (hg : g < 149) :
    ∃ r ∈ VREP, ∃ cc < 6720, vlConjEq r g cc = true ∧
      eqRows (mulRows vlCx[cc]! vlCxInv[cc]!) (idRows ()) = true := by
  have hv' := hv g hg
  unfold vcK at hv'
  simp only [andB_eq, Bool.and_eq_true] at hv'
  obtain ⟨hr, hr', hcc, -, hcan, hm, hs⟩ := hv'
  refine ⟨_, inLK_mem' hr, _, lt_of_blt hcc, ?_, ?_⟩
  · rw [conjEq_eq h hl (lt_of_blt hr') hg (lt_of_blt hcc) hcan hm]
    exact hs
  · rw [eqRows_of (mul_enc hK (cx_enc (lt_of_blt hcc)) (cxi_enc (lt_of_blt hcc) hcan hm))
      (id_enc hK)]
    exact hm

theorem any_of_mem {L : List (Array V2)} (hw : ∀ M ∈ L, WfA M) {X : Array V2} {x : Nat}
    (hX : WfA X ∧ encR X = x) (hx : x ∈ L.map encR) : ∃ K ∈ L, eqRows X K = true := by
  obtain ⟨K, hK', e⟩ := List.mem_map.1 hx
  refine ⟨K, hK', ?_⟩
  rw [eqRows_of hX ⟨hw K hK', rfl⟩, e]
  exact Nat.beq_refl _

theorem mem_of_allLK {f : Nat → Bool} {l : List Nat} (h : allLK f l = true) {x : Nat} (hx : x ∈ l) :
    f x = true := by
  rw [allLK_eq, List.all_eq_true] at h
  exact h x hx

@[expose] def NgEnc (k : Nat) (T0 T1 T2 T3 : Array V2) : Prop :=
  (WfA T0 ∧ encR T0 = ngK k 0) ∧ (WfA T1 ∧ encR T1 = ngK k 1) ∧ (WfA T2 ∧ encR T2 = ngK k 2) ∧
    (WfA T3 ∧ encR T3 = ngK k 3)

theorem ng_get {k : Nat} {T0 T1 T2 T3 : Array V2} (hT : NgEnc k T0 T1 T2 T3) {i : Nat} (hi : i < 4) :
    WfA (#[T0, T1, T2, T3][i]!) ∧ encR (#[T0, T1, T2, T3][i]!) = ngK k i := by
  obtain ⟨h0, h1, h2, h3⟩ := hT
  interval_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem sub_list_enc {k : Nat} {T0 T1 T2 T3 : Array V2} (hT : NgEnc k T0 T1 T2 T3) :
    (∀ m, WfA (vlSubsetProd #[T0, T1, T2, T3] m) ∧
      encR (vlSubsetProd #[T0, T1, T2, T3] m) = getN one (nsK k) m ∨ 16 ≤ m) ∧
    (∀ M ∈ (List.range 16).map (vlSubsetProd #[T0, T1, T2, T3]), WfA M) ∧
      ((List.range 16).map (vlSubsetProd #[T0, T1, T2, T3])).map encR = nsK k := by
  obtain ⟨h0, h1, h2, h3⟩ := hT
  have hS := sub_enc h0 h1 h2 h3
  have he : ((List.range 16).map (vlSubsetProd #[T0, T1, T2, T3])).map encR = nsK k := by
    rw [List.map_map]
    unfold nsK d4SK
    rw [smapK_eq, rangeK_eq]
    refine List.map_congr_left fun m _ => ?_
    rw [Function.comp_apply, sub_eq, (hS m).2]
  refine ⟨fun m => ?_, fun M hM => ?_, he⟩
  · by_cases hm : m < 16
    · left
      refine ⟨by rw [sub_eq]; exact (hS m).1, ?_⟩
      rw [← he, getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
        List.getElem?_range hm]
      rfl
    · exact Or.inr (by omega)
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hM
    rw [sub_eq]
    exact (hS m).1

theorem sub_enc' {k : Nat} {T0 T1 T2 T3 : Array V2} (hT : NgEnc k T0 T1 T2 T3) {m : Nat}
    (hm : m < 16) : WfA (vlSubsetProd #[T0, T1, T2, T3] m) ∧
      encR (vlSubsetProd #[T0, T1, T2, T3] m) = getN one (nsK k) m := by
  rcases (sub_list_enc hT).1 m with h | h
  · exact h
  · omega

theorem sameSet_eq {k : Nat} {T0 T1 T2 T3 : Array V2} (hT : NgEnc k T0 T1 T2 T3)
    {B : Array (Array V2)} (hB : ∀ M ∈ B.toList, WfA M) :
    vlSameSet #[T0, T1, T2, T3] B = sameK (nsK k) (B.toList.map encR) := by
  obtain ⟨-, hw, he⟩ := sub_list_enc hT
  unfold vlSameSet sameK
  simp only [← Array.all_toList, ← Array.any_toList]
  rw [allAny_enc hw hB, allAny_enc hB hw, he, andB_eq]

theorem nmK_parts {k : Nat} (hn : nmK k = true) :
    closedK (gaK (getN 0 VREP k)) = true ∧ Nat.beq (lenK (gaK (getN 0 VREP k))) 16 = true ∧
      (∀ i < 4, inLK (ngK k i) (gaK (getN 0 VREP k)) = true) ∧
      allLK (fun s => inLK s (gaK (getN 0 VREP k))) (nsK k) = true ∧ distK (nsK k) = true ∧
      getN 0 VREP k < 149 ∧ sameK (nsK k) (gaK (getN 0 VREP k)) = true ∧
      ∀ g < getN 0 VREP k, sameK (nsK k) (gaK g) = false := by
  unfold nmK at hn
  beta_reduce at hn
  simp only [andB_eq, Bool.and_eq_true] at hn
  obtain ⟨hc, hl, hg, hs, hd, hr, hsr, hlt⟩ := hn
  refine ⟨hc, hl, allR_spec hg, hs, hd, lt_of_blt hr, hsr, fun g hg' => ?_⟩
  have := allR_spec hlt g hg'
  rw [notB_eq, Bool.not_eq_true'] at this
  exact this

theorem idxOf_eq (h : VlK4011) (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true)
    {k : Nat} {T0 T1 T2 T3 : Array V2} (hT : NgEnc k T0 T1 T2 T3) (hn : nmK k = true) :
    vlIdxOf #[T0, T1, T2, T3] = getN 0 VREP k := by
  obtain ⟨-, -, -, -, -, hr, hsr, hlt⟩ := nmK_parts hn
  have hp : ∀ g < 149, vlSameSet #[T0, T1, T2, T3] vlAll[g]! = sameK (nsK k) (gaK g) :=
    fun g hg => by rw [sameSet_eq hT (vlAll_enc h hl hg).1, (vlAll_enc h hl hg).2]
  unfold vlIdxOf
  rw [vlAll_size' h]
  have e : (List.range 149).find? (fun g => vlSameSet #[T0, T1, T2, T3] vlAll[g]!) =
      some (getN 0 VREP k) := by
    rw [List.find?_range_eq_some]
    refine ⟨by rw [hp _ hr]; exact hsr, List.mem_range.2 hr, fun j hj => ?_⟩
    rw [hp j (by omega), hlt j hj]
    rfl
  rw [e]
  rfl

@[expose] def namedTest (r : Nat) (gs : Array (Array V2)) : Bool :=
  let A := vlAll[r]!
  vrClosedB A && A.size == 16 &&
    (List.range 4).all (fun i => CFSG.Sporadic.J4.QT2.wfRows (gs[i]!) && A.any (eqRows (gs[i]!))) &&
    (List.range 16).all (fun m => A.any (eqRows (vlSubsetProd gs m))) &&
    (List.range 16).all fun m => (List.range 16).all fun m' =>
      !(eqRows (vlSubsetProd gs m) (vlSubsetProd gs m')) || m == m'

theorem named_one (h : VlK4011) (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true)
    {k : Nat} {T0 T1 T2 T3 : Array V2} (hT : NgEnc k T0 T1 T2 T3) (hn : nmK k = true) :
    namedTest (getN 0 VREP k) #[T0, T1, T2, T3] = true := by
  unfold namedTest
  obtain ⟨hc, hlen, hg, hs, hd, hr, -, -⟩ := nmK_parts hn
  obtain ⟨hw, he⟩ := vlAll_enc h hl hr
  set A := vlAll[getN 0 VREP k]! with hA
  have hmem : ∀ {X : Array V2} {x : Nat}, WfA X ∧ encR X = x → inLK x (gaK (getN 0 VREP k)) = true →
      A.any (eqRows X) = true := fun hX hx => by
    rw [← Array.any_toList, List.any_eq_true]
    exact any_of_mem hw hX (he ▸ inLK_mem' hx)
  unfold closedK at hc
  rw [andB_eq, Bool.and_eq_true] at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩, fun m hm => ?_⟩, fun m hm m' hm' => ?_⟩
  · unfold vrClosedB
    simp only [Bool.and_eq_true, ← Array.all_toList, List.all_eq_true]
    refine ⟨hmem (id_enc hK) hc.1, fun M hM => ?_⟩
    have hMe : encR M ∈ gaK (getN 0 VREP k) := he ▸ List.mem_map_of_mem hM
    have hx := mem_of_allLK hc.2 hMe
    rw [andB_eq, Bool.and_eq_true] at hx
    refine ⟨?_, fun N hN => ?_⟩
    · rw [eqRows_of (mul_enc hK ⟨hw M hM, rfl⟩ ⟨hw M hM, rfl⟩) (id_enc hK)]
      exact hx.1
    · have hNe : encR N ∈ gaK (getN 0 VREP k) := he ▸ List.mem_map_of_mem hN
      exact hmem (mul_enc hK ⟨hw M hM, rfl⟩ ⟨hw N hN, rfl⟩) (mem_of_allLK hx.2 hNe)
  · have hl' := congrArg List.length he
    rw [List.length_map, Array.length_toList, ← lenK_eq, Nat.eq_of_beq_eq_true hlen] at hl'
    rw [hl']
    rfl
  · unfold CFSG.Sporadic.J4.QT2.wfRows
    exact wf_bool (ng_get hT hi).1
  · exact hmem (ng_get hT hi) (hg i hi)
  · obtain ⟨-, -, hse⟩ := sub_list_enc hT
    have hx : getN one (nsK k) m ∈ nsK k := by
      rw [← hse, getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hm)]
      exact List.getElem_mem _
    exact hmem (sub_enc' hT hm) (mem_of_allLK hs hx)
  · rw [eqRows_of (sub_enc' hT hm) (sub_enc' hT hm'), Bool.or_eq_true, beq_iff_eq]
    rcases Nat.lt_trichotomy m m' with hlt | heq | hgt
    · left
      have := allR_spec (allR_spec hd m' hm') m hlt
      rw [notB_eq] at this
      rw [beq_comm']
      exact this
    · exact Or.inr heq
    · left
      have := allR_spec (allR_spec hd m hm) m' hgt
      rw [notB_eq] at this
      exact this

theorem vlW5_eq : vlW5 = w5 := rfl

theorem b7Decode_eq : CFSG.QuasithinUnique.A5.B7.b7Decode = w5 := rfl

theorem a941_eq : vlA941Strs.map vlW5 = vA9W := by
  rw [VA9.eq, vlW5_eq]
  simp only [List.map_cons, List.map_nil, ← String.ofList_append, w5_ofList, vA9W,
    List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

theorem b7w_eq : CFSG.QuasithinUnique.A5.B7.b7ExplicitWords = vB7W := by
  rw [VB7.eq, b7Decode_eq]
  simp only [← String.ofList_append, w5_ofList, vB7W, List.flatten_cons, List.flatten_nil,
    List.append_nil, List.append_assoc]

theorem bsw_eq : vlB336Word = vBSW := by
  rw [VBS.eq, vlW5_eq, w5_ofList]
  rfl

@[expose] def NgK : Prop :=
  ngMaskOK = true ∧ ngB3OK = true ∧ (∀ i < 4, ngA9OK i = true) ∧ (∀ i < 4, ngB7OK i = true) ∧
    ∀ j < 4, ngXiOK j = true

theorem ef_lit (h : VlK4011) {e : Nat} (he : e < 2048) {n : Nat} (hn : Nat.beq n (CFSG.KD.ETA.EF e) = true) :
    WfA (etaE e) ∧ encR (etaE e) = n :=
  ⟨(ef_enc h.2.1 he).1, (ef_enc h.2.1 he).2.trans (Nat.eq_of_beq_eq_true hn).symm⟩

theorem word_lit {w : List Int} {n : Nat} (hn : Nat.beq n (wordJ c rm one G5 G5i w) = true) :
    WfA (wR w) ∧ encR (wR w) = n :=
  ⟨(wR_enc w).1, (wR_enc w).2.trans (Nat.eq_of_beq_eq_true hn).symm⟩

theorem masks_enc (h : VlK4011) (hg : NgK) {k o : Nat} (hk : k = 0 ∧ o = 0 ∨ k = 1 ∧ o = 4 ∨ k = 5 ∧ o = 8) :
    NgEnc k (etaE (getN 0 ngMasks o)) (etaE (getN 0 ngMasks (o + 1))) (etaE (getN 0 ngMasks (o + 2)))
      (etaE (getN 0 ngMasks (o + 3))) := by
  have hm := hg.1
  unfold ngMaskOK at hm
  have hq : ∀ i < 4, Nat.beq (ngK k i) (CFSG.KD.ETA.EF (getN 0 ngMasks (o + i))) = true := by
    intro i hi
    have hi' := allR_spec hm i hi
    simp only [andB_eq, Bool.and_eq_true] at hi'
    rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [Nat.zero_add]
      exact hi'.1
    · exact hi'.2.1
    · exact hi'.2.2
  have hlt : ∀ i < 4, getN 0 ngMasks (o + i) < 2048 := by
    intro i hi
    rcases hk with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> interval_cases i <;> decide
  exact ⟨ef_lit h (hlt 0 (by decide)) (hq 0 (by decide)), ef_lit h (hlt 1 (by decide)) (hq 1 (by decide)),
    ef_lit h (hlt 2 (by decide)) (hq 2 (by decide)), ef_lit h (hlt 3 (by decide)) (hq 3 (by decide))⟩

theorem words_enc {k : Nat} {W : List (List Int)} (hq : ∀ i < 4, Nat.beq (ngK k i)
    (wordJ c rm one G5 G5i (getW W i)) = true) :
    NgEnc k (wR (getW W 0)) (wR (getW W 1)) (wR (getW W 2)) (wR (getW W 3)) :=
  ⟨word_lit (hq 0 (by decide)), word_lit (hq 1 (by decide)), word_lit (hq 2 (by decide)),
    word_lit (hq 3 (by decide))⟩

theorem xi_enc' (h : VlK4011) (hg : NgK) {j : Nat} (hj : j < 4) :
    NgEnc (6 + j) (mulRows (etaE (getN 0 ngXiMasks j)) (wR vlB336Word))
      (vlXiConj (mulRows (etaE (getN 0 ngXiMasks j)) (wR vlB336Word)))
      (vlXiConj (vlXiConj (mulRows (etaE (getN 0 ngXiMasks j)) (wR vlB336Word))))
      (vlXiConj (vlXiConj (vlXiConj (mulRows (etaE (getN 0 ngXiMasks j)) (wR vlB336Word))))) := by
  have hx := hg.2.2.2.2 j hj
  unfold ngXiOK at hx
  beta_reduce at hx
  rw [andB_eq, Bool.and_eq_true] at hx
  obtain ⟨h0, h1⟩ := hx
  have he : getN 0 ngXiMasks j < 2048 := by interval_cases j <;> decide
  have t0 : WfA (mulRows (etaE (getN 0 ngXiMasks j)) (wR vlB336Word)) ∧
      encR (mulRows (etaE (getN 0 ngXiMasks j)) (wR vlB336Word)) = ngK (6 + j) 0 := by
    have := mul_enc hK (ef_enc h.2.1 he) (wR_enc vlB336Word)
    rw [bsw_eq] at this ⊢
    exact ⟨this.1, this.2.trans (Nat.eq_of_beq_eq_true h0).symm⟩
  have step : ∀ i < 3, ∀ {T : Array V2}, WfA T ∧ encR T = ngK (6 + j) i →
      WfA (vlXiConj T) ∧ encR (vlXiConj T) = ngK (6 + j) (i + 1) := fun i hi T hT =>
    ⟨(xiConj_enc hT).1, (xiConj_enc hT).2.trans (Nat.eq_of_beq_eq_true (allR_spec h1 i hi)).symm⟩
  have t1 := step 0 (by decide) t0
  have t2 := step 1 (by decide) t1
  exact ⟨t0, t1, t2, step 2 (by decide) t2⟩

theorem named_enc (h : VlK4011) (hg : NgK) {k : Nat} (hk : k < 10) :
    ∃ T0 T1 T2 T3, vlNamedGs[k]! = #[T0, T1, T2, T3] ∧ NgEnc k T0 T1 T2 T3 := by
  interval_cases k
  · refine ⟨_, _, _, _, ?_, masks_enc h hg (Or.inl ⟨rfl, rfl⟩)⟩
    change gsMasks vlA21Masks = _
    rfl
  · refine ⟨_, _, _, _, ?_, masks_enc h hg (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
    change gsMasks vlA77Masks = _
    rfl
  · refine ⟨_, _, _, _, ?_, words_enc (W := vA9W) fun i hi => hg.2.2.1 i hi⟩
    change gsWords (vlA941Strs.map vlW5) = _
    rw [a941_eq]
    rfl
  · refine ⟨_, _, _, _, ?_, words_enc (W := vB7W) fun i hi => hg.2.2.2.1 i hi⟩
    change gsWords CFSG.QuasithinUnique.A5.B7.b7ExplicitWords = _
    rw [b7w_eq]
    rfl
  · have hb := hg.2.1
    unfold ngB3OK at hb
    have hq : ∀ i < 4, WfA (wR (CFSG.QuasithinUnique.A5.Dec2.wsB336.getD i [])) ∧
        encR (wR (CFSG.QuasithinUnique.A5.Dec2.wsB336.getD i [])) = ngK 4 i := fun i hi =>
      ⟨(b3_hG i hi).1, (b3_hG i hi).2.trans (Nat.eq_of_beq_eq_true (allR_spec hb i hi)).symm⟩
    refine ⟨_, _, _, _, ?_, hq 0 (by decide), hq 1 (by decide), hq 2 (by decide), hq 3 (by decide)⟩
    change gsWords CFSG.QuasithinUnique.A5.Dec2.wsB336 = _
    unfold gsWords CFSG.QuasithinUnique.A5.Dec2.wsB336
    rfl
  · refine ⟨_, _, _, _, ?_, masks_enc h hg (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    change gsMasks vlB56Masks = _
    rfl
  · refine ⟨_, _, _, _, ?_, xi_enc' h hg (j := 0) (by decide)⟩
    change gsXi 37 = _
    rfl
  · refine ⟨_, _, _, _, ?_, xi_enc' h hg (j := 1) (by decide)⟩
    change gsXi 97 = _
    rfl
  · refine ⟨_, _, _, _, ?_, xi_enc' h hg (j := 2) (by decide)⟩
    change gsXi 236 = _
    rfl
  · refine ⟨_, _, _, _, ?_, xi_enc' h hg (j := 3) (by decide)⟩
    change gsXi 491 = _
    rfl

theorem vlNamedGs_len' : vlNamedGs.length = 10 := rfl

theorem vrep_len : VREP.length = 10 := rfl

theorem named_of (h : VlK4011) (hl : allR 272 (fun i => Nat.blt (getN 0 IL17 i) 2048) = true)
    (hg : NgK) (hn : ∀ k < 10, nmK k = true) : chkNamed = true ∧ vlRepIdx = VREP := by
  have hidx : ∀ k < 10, vlIdxOf vlNamedGs[k]! = getN 0 VREP k := by
    intro k hk
    obtain ⟨T0, T1, T2, T3, e, hT⟩ := named_enc h hg hk
    rw [e]
    exact idxOf_eq h hl hT (hn k hk)
  have hmap : vlNamedGs.map vlIdxOf = VREP := by
    refine List.ext_getElem (by rw [List.length_map, vlNamedGs_len', vrep_len]) fun k h1 h2 => ?_
    have hk : k < 10 := by rwa [List.length_map, vlNamedGs_len'] at h1
    rw [List.getElem_map, ← getElem!_pos vlNamedGs k (by rw [vlNamedGs_len']; exact hk), hidx k hk,
      getN_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  have hrep : vlRepIdx = VREP := by
    unfold vlRepIdx vlPref
    rw [List.map_take, hmap]
    rfl
  refine ⟨?_, hrep⟩
  unfold chkNamed
  rw [hmap, hrep, Bool.and_eq_true]
  refine ⟨beq_self_eq_true _, List.all_eq_true.2 fun x hx => ?_⟩
  change namedTest x.1 x.2 = true
  obtain ⟨r, gs⟩ := x
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
  rw [List.getElem?_zip_eq_some] at hk
  obtain ⟨h1, h2⟩ := hk
  have hkV : k < VREP.length := (List.getElem?_eq_some_iff.1 h1).1
  have hk' : k < 10 := by rw [vrep_len] at hkV; exact hkV
  have hkN : k < vlNamedGs.length := by rw [vlNamedGs_len']; exact hk'
  obtain ⟨T0, T1, T2, T3, e, hT⟩ := named_enc h hg hk'
  have er : r = getN 0 VREP k := by
    rw [getN_eq_getD, List.getD_eq_getElem?_getD, h1, Option.getD_some]
  have eg : gs = #[T0, T1, T2, T3] := by
    rw [← e, getElem!_pos vlNamedGs k hkN]
    exact (Option.some.inj ((List.getElem?_eq_getElem hkN).symm.trans h2)).symm
  rw [er, eg]
  exact named_one h hl hT (hn k hk')

end CertificateChecks.KernelJ4Q

end

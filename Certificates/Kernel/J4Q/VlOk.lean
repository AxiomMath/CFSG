module

public import Certificates.Kernel.J4Q.VlBase
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.A5

def VecOK (x : Nat) : Prop := ∃ v : V2, v.wf = true ∧ v2N v = x

def MatOK (m : Nat) : Prop := ∃ M : Array V2, WfA M ∧ encR M = m

theorem matOK_of {M : Array V2} {m : Nat} (h : WfA M ∧ encR M = m) : MatOK m := ⟨M, h⟩

theorem mulJ_ok {a b : Nat} (ha : MatOK a) (hb : MatOK b) : MatOK (mulJ c rm a b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨_, mul_enc hK hA hB⟩

theorem vecJ_ok {x m : Nat} (hx : VecOK x) (hm : MatOK m) : VecOK (vecJ rm x m) := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨M, hM, rfl⟩ := hm
  exact ⟨_, wf_frApply hM v, v2N_frApply hK hM hv⟩

theorem vecJ_mulJ {x a b : Nat} (hx : VecOK x) (ha : MatOK a) (hb : MatOK b) :
    vecJ rm x (mulJ c rm a b) = vecJ rm (vecJ rm x a) b := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  rw [← enc_mulRows hK hA hB, ← v2N_frApply hK (wf_mulRows hA hB) hv, vec_mulRows hA hB hv,
    v2N_frApply hK hB (wf_frApply hA v), v2N_frApply hK hA hv]

theorem xi_enc : WfA (x0GenRows[0]!) ∧ encR (x0GenRows[0]!) = xiV := x0Gen_enc (i := 0) (by decide)

theorem xiI_enc : WfA (x0InvRows[0]!) ∧ encR (x0InvRows[0]!) = xiIV := x0Inv_enc (i := 0) (by decide)

theorem w0_ok : VecOK W0 := ⟨rootV, rootV_wf', rfl⟩

theorem xiConj_enc {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) :
    WfA (vlXiConj T) ∧ encR (vlXiConj T) = cjV t :=
  mul_enc hK (mul_enc hK xi_enc hT) xiI_enc

theorem vlValid_eq {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) : vlValid T = vValidK t := by
  have h1 := xiConj_enc hT
  have h2 := xiConj_enc h1
  have h3 := xiConj_enc h2
  have h4 := xiConj_enc h3
  unfold vlValid vlComm
  dsimp only
  rw [eqRows_of (mul_enc hK hT hT) (id_enc hK), eqRows_of (mul_enc hK hT h1) (mul_enc hK h1 hT),
    eqRows_of (mul_enc hK hT h2) (mul_enc hK h2 hT),
    eqRows_of (mul_enc hK (mul_enc hK (mul_enc hK (mul_enc hK hT h1) h2) h3) h4) (id_enc hK)]
  unfold vValidK
  simp only [andB_eq]

theorem vpK_eq {j e : Nat} (hE : MatOK (CFSG.KD.ETA.EF e)) (hS : MatOK (getN one VLS j)) :
    vpK j e = vValidK (tK j e) := by
  have hT : MatOK (tK j e) := mulJ_ok hE hS
  have vt : ∀ v, VecOK v → vtK v j e = vecJ rm v (tK j e) := fun v hv => (vecJ_mulJ hv hE hS).symm
  have hX : MatOK xiV := matOK_of xi_enc
  have hXI : MatOK xiIV := matOK_of xiI_enc
  have hT1 : MatOK (cjV (tK j e)) := mulJ_ok (mulJ_ok hX hT) hXI
  have vx : ∀ v, VecOK v → vxK v j e = vecJ rm v (cjV (tK j e)) := fun v hv => by
    unfold vxK
    rw [vt _ (vecJ_ok hv hX), ← vecJ_mulJ hv hX hT, ← vecJ_mulJ hv (mulJ_ok hX hT) hXI]
    rfl
  cases hV : vValidK (tK j e)
  · unfold vpK
    rw [hV]
    cases Nat.beq (vtK (vtK W0 j e) j e) (vecJ rm W0 one) <;>
      cases Nat.beq (vxK (vtK W0 j e) j e) (vtK (vxK W0 j e) j e) <;> rfl
  · have hV' := hV
    unfold vValidK at hV'
    simp only [andB_eq, Bool.and_eq_true] at hV'
    obtain ⟨hsq, ⟨hc1, -⟩, -⟩ := hV'
    have w1 := vecJ_ok w0_ok hT
    have w2 := vecJ_ok w0_ok hT1
    unfold vpK
    rw [hV, vt _ w0_ok, vt _ w1, vx _ w1, vx _ w0_ok, vt _ w2, ← vecJ_mulJ w0_ok hT hT,
      Nat.eq_of_beq_eq_true hsq, ← vecJ_mulJ w0_ok hT hT1, ← vecJ_mulJ w0_ok hT1 hT,
      Nat.eq_of_beq_eq_true hc1, Nat.beq_refl, Nat.beq_refl]
    rfl

theorem ef_enc (hE : ∀ t < 32, etaCK t = true) {e : Nat} (he : e < 2048) :
    WfA (etaE e) ∧ encR (etaE e) = CFSG.KD.ETA.EF e := by
  have h := allR_spec (hE (e / 64) (by omega)) (e % 64) (Nat.mod_lt _ (by decide))
  have ee : Nat.add (Nat.mul 64 (e / 64)) (e % 64) = e := by
    change 64 * (e / 64) + e % 64 = e
    omega
  beta_reduce at h
  rw [ee] at h
  exact ⟨(etaE_enc e).1, (etaE_enc e).2.trans (Nat.eq_of_beq_eq_true h).symm⟩

theorem vlJ_of {j : Nat} (h : vlJK j = true) :
    (liftW 200 (getN 0 VLI j)).all (fun l => letters.contains l) = true ∧
      (wordT (liftW 200 (getN 0 VLI j)) == iTS (getN 0 VLI j)) = true ∧
      getN one VLS j = wordJ c rm one G5 G5i (liftW 200 (getN 0 VLI j)) := by
  unfold vlJK at h
  beta_reduce at h
  simp only [andB_eq, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem lift_enc (hJ : ∀ j < 75, vlJK j = true) {j : Nat} (hj : j < 75) :
    WfA (wR (vlLiftWord (iTS (getN 0 VLI j)))) ∧
      encR (wR (vlLiftWord (iTS (getN 0 VLI j)))) = getN one VLS j := by
  rw [vlLiftWord_eq (vli_lt hj)]
  exact ⟨(wR_enc _).1, (wR_enc _).2.trans (vlJ_of (hJ j hj)).2.2.symm⟩

theorem tab_mem {j : Nat} (hj : j < 75) : iTS (getN 0 VLI j) ∈ vlTables := by
  rw [vlTables_eq]
  exact List.mem_map_of_mem (List.mem_range.2 hj)

theorem liftRows_eq {y : List Nat} (hy : y ∈ vlTables) : vlLiftRows y = wR (vlLiftWord y) := by
  have hs : (vlTables.findIdx? (· == y)).isSome = true := by
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨y, hy, beq_self_eq_true y⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨hl, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
  have hy' : vlTables[i] = y := beq_iff_eq.1 hp
  unfold vlLiftRows vlTabIdx vlLiftTab
  rw [hi, Option.getD_some, getElem!_pos _ i (by simp [hl])]
  simp [hy']

theorem vlEta_get {e : Nat} (he : e < 2048) : vlEtaTab[e]! = etaE e := by
  unfold vlEtaTab
  rw [getElem!_pos _ e (by simp [he])]
  simp [etaE]

theorem filterMap_ite {α β : Type} (p : α → Bool) (g : α → β) : ∀ l : List α,
    l.filterMap (fun a => if p a then some (g a) else none) = (l.filter p).map g
  | [] => rfl
  | a :: l => by
    cases h : p a <;> simp [h, filterMap_ite p g l]

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x List.mem_cons_self,
      flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem filter_congr' {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.filter p = l.filter q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filter_cons, List.filter_cons, h x List.mem_cons_self,
      filter_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem range2048_chk : (List.range 2048 ==
    (List.range 32).flatMap fun c' => (List.range 64).map (Nat.add (Nat.mul 64 c'))) = true := by
  quickRfl

theorem vlel_chk : allR 75 (fun j => getLV VLEL j == (List.range 32).flatMap fun c' =>
    (getLV VLEL j).filter fun e => andB (Nat.ble (Nat.mul 64 c') e) (Nat.blt e (Nat.add (Nat.mul 64 c') 64))) =
    true := by quickRfl

theorem seg_of (hS : ∀ t < 256, segK t = true) {j c' : Nat} (hj : j < 75) (hc : c' < 32) :
    segAt j c' = true := by
  have ht : 8 * c' + j / 10 < 256 := by omega
  have h := allR_spec (hS _ ht) (j % 10) (Nat.mod_lt _ (by decide))
  have e1 : Nat.div (8 * c' + j / 10) 8 = c' := by
    change (8 * c' + j / 10) / 8 = c'
    omega
  have e2 : Nat.add (Nat.mul 10 (Nat.mod (8 * c' + j / 10) 8)) (j % 10) = j := by
    change 10 * ((8 * c' + j / 10) % 8) + j % 10 = j
    omega
  beta_reduce at h
  rw [e1, e2] at h
  have hb : Nat.blt j 75 = true := Nat.ble_eq_true_of_le hj
  rw [hb] at h
  exact h

theorem valid_filter (hS : ∀ t < 256, segK t = true) {j : Nat} (hj : j < 75) :
    (List.range 2048).filter (vpK j) = getL VLEL j := by
  have hv := beq_iff_eq.1 (allR_spec vlel_chk j hj)
  have e : getL VLEL j = getLV VLEL j := rfl
  rw [beq_iff_eq.1 range2048_chk, List.filter_flatMap, e, hv]
  refine flatMap_congr' fun c' hc => ?_
  exact beq_iff_eq.1 (seg_of hS hj (List.mem_range.1 hc))

theorem ql_mem (hS : ∀ t < 256, segK t = true) {q : Nat × Nat} (hq : q ∈ QL) :
    q.1 < 75 ∧ q.2 < 2048 := by
  unfold QL at hq
  obtain ⟨j, hj, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hq
  have hj' := List.mem_range.1 hj
  rw [← valid_filter hS hj'] at he
  exact ⟨hj', List.mem_range.1 (List.mem_filter.1 he).1⟩

theorem vlPairs_eq (hJ : ∀ j < 75, vlJK j = true) (hE : ∀ t < 32, etaCK t = true)
    (hS : ∀ t < 256, segK t = true) :
    vlPairs = QL.map fun q => (iTS (getN 0 VLI q.1), q.2) := by
  unfold vlPairs QL
  rw [vlTables_eq, List.flatMap_map, List.map_flatMap]
  refine flatMap_congr' fun j hj => ?_
  have hj' := List.mem_range.1 hj
  dsimp only
  rw [filterMap_ite, List.map_map, ← valid_filter hS hj']
  congr 1
  refine filter_congr' fun e he => ?_
  have he' := List.mem_range.1 he
  rw [vlEta_get he', liftRows_eq (tab_mem hj'),
    vlValid_eq (mul_enc hK (ef_enc hE he') (lift_enc hJ hj'))]
  exact (vpK_eq (matOK_of (ef_enc hE he')) (matOK_of (lift_enc hJ hj'))).symm

theorem sub_eq (a b c' d : Array V2) (m : Nat) : vlSubsetProd #[a, b, c', d] m = d4Sub [a, b, c', d] m := by
  have hg : ∀ i, #[a, b, c', d][i]! = [a, b, c', d].getD i #[] := by
    intro i
    rcases i with _ | _ | _ | _ | i
    all_goals simp
    rfl
  unfold vlSubsetProd d4Sub
  simp only [hg]

theorem group_enc {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) :
    (∀ M ∈ vlGroupOf T, WfA M) ∧ (vlGroupOf T).map encR = gK t := by
  have h1 : WfA (vlXiConj T) ∧ encR (vlXiConj T) = cjK t := xiConj_enc hT
  have h2 : WfA (vlXiConj (vlXiConj T)) ∧ encR (vlXiConj (vlXiConj T)) = cjK (cjK t) := xiConj_enc h1
  have h3 : WfA (vlXiConj (vlXiConj (vlXiConj T))) ∧
      encR (vlXiConj (vlXiConj (vlXiConj T))) = cjK (cjK (cjK t)) := xiConj_enc h2
  have hS := sub_enc hT h1 h2 h3
  unfold vlGroupOf vlConjs
  dsimp only
  refine ⟨fun M hM => ?_, ?_⟩
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hM
    rw [sub_eq]
    exact (hS m).1
  · rw [List.map_map]
    unfold gK d4SK
    beta_reduce
    rw [smapK_eq, rangeK_eq]
    refine List.map_congr_left fun m _ => ?_
    rw [Function.comp_apply, sub_eq, (hS m).2]

theorem any_idx {α : Type} (d : α) (f : α → Bool) (l : List α) :
    l.any f = (List.range l.length).any fun i => f (l.getD i d) := by
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨x, hx, hf⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact ⟨i, hi, by simpa [List.getD_eq_getElem?_getD, hi] using hf⟩
  · rintro ⟨i, hi, hf⟩
    exact ⟨l[i], List.getElem_mem hi, by simpa [List.getD_eq_getElem?_getD, hi] using hf⟩

@[expose] def GInv (p : Nat) (acc : List (List (Array V2))) : Prop :=
  acc.length = getN 0 VLC p ∧
    ∀ h < getN 0 VLC p, (∀ M ∈ acc.getD h [], WfA M) ∧ (acc.getD h []).map encR = grpK h

theorem any_grp {G : List (Array V2)} {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t)
    (hw : ∀ M ∈ G, WfA M) : G.any (eqRows T) = (G.map encR).any (Nat.beq t) := by
  rw [List.any_map]
  exact any_congr_mem4 fun M hM => eqRows_of hT ⟨hw M hM, rfl⟩

theorem any_acc {acc : List (List (Array V2))} {p : Nat} (hI : GInv p acc) {T : Array V2} {t : Nat}
    (hT : WfA T ∧ encR T = t) :
    acc.any (fun G => G.any (eqRows T)) =
      (List.range (getN 0 VLC p)).any fun h => (grpK h).any (Nat.beq t) := by
  rw [any_idx [] _ acc, hI.1]
  refine any_congr_mem4 fun h hh => ?_
  have hh' := List.mem_range.1 hh
  rw [any_grp hT (hI.2 h hh').1, (hI.2 h hh').2]

theorem fold_inv {β : Type} {F : List (List (Array V2)) → β → List (List (Array V2))}
    {P : List β} {Inv : Nat → List (List (Array V2)) → Prop} (h0 : Inv 0 [])
    (hs : ∀ p (hp : p < P.length) acc, Inv p acc → Inv (p + 1) (F acc (P[p]'hp))) :
    ∀ p ≤ P.length, Inv p ((P.take p).foldl F []) := by
  intro p
  induction p with
  | zero => intro _; simpa using h0
  | succ p ih =>
    intro hp
    rw [List.take_add_one, List.foldl_append, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.foldl_cons, List.foldl_nil]
    exact hs p (by omega) _ (ih (by omega))

theorem vlc_chk : andB (Nat.beq (getN 0 VLC 0) 0) (andB (Nat.beq (getN 0 VLC 1980) 132)
    (Nat.beq QL.length 1980)) = true := by quickRfl

theorem vlc0 : getN 0 VLC 0 = 0 := by
  have h := vlc_chk
  simp only [andB_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem vlc1980 : getN 0 VLC 1980 = 132 := by
  have h := vlc_chk
  simp only [andB_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.1

theorem ql_len : QL.length = 1980 := by
  have h := vlc_chk
  simp only [andB_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.2.2

theorem pair_enc (hJ : ∀ j < 75, vlJK j = true) (hE : ∀ t < 32, etaCK t = true)
    (hS : ∀ t < 256, segK t = true) {p : Nat} (hp' : p < vlPairs.length) :
    WfA (vlT vlPairs[p]) ∧ encR (vlT vlPairs[p]) = tKp p := by
  have hP := vlPairs_eq hJ hE hS
  have hl : p < QL.length := by
    have := hp'
    rw [hP, List.length_map] at this
    exact this
  have hq := ql_mem hS (List.getElem_mem hl)
  have e : vlPairs[p] = (iTS (getN 0 VLI QL[p].1), QL[p].2) := by
    simp only [hP, List.getElem_map]
  have et : tKp p = tK QL[p].1 QL[p].2 := by
    unfold tKp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  rw [e, et]
  unfold vlT
  dsimp only
  rw [vlEta_get hq.2, liftRows_eq (tab_mem hq.1)]
  exact mul_enc hK (ef_enc hE hq.2) (lift_enc hJ hq.1)

theorem pairAt_parts {p : Nat} (h : pairAtK p = true) :
    distK (gK (tKp p)) = true ∧ getN 0 VLH p < 132 ∧
      (gK (tKp p)).all (fun x => (grpK (getN 0 VLH p)).any (Nat.beq x)) = true ∧
      (Nat.beq (getN 0 VLN p) 1 = false → getN 0 VLH p < getN 0 VLC p ∧
        getN 0 VLC (p + 1) = getN 0 VLC p ∧ (grpK (getN 0 VLH p)).any (Nat.beq (tKp p)) = true) ∧
      (Nat.beq (getN 0 VLN p) 1 = true → getN 0 VLC (p + 1) = getN 0 VLC p + 1 ∧
        (List.range (getN 0 VLC p)).any (fun h' => (grpK h').any (Nat.beq (tKp p))) = false ∧
        gK (tKp p) = grpK (getN 0 VLC p)) := by
  unfold pairAtK at h
  beta_reduce at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hd, hh, hall, -, hr⟩ := h
  refine ⟨hd, lt_of_blt hh, hall, fun hb => ?_, fun hb => ?_⟩
  · rw [hb] at hr
    dsimp only at hr
    simp only [Bool.and_eq_true] at hr
    exact ⟨lt_of_blt hr.1, Nat.eq_of_beq_eq_true hr.2.1, hr.2.2⟩
  · rw [hb] at hr
    dsimp only at hr
    simp only [Bool.and_eq_true, notB_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hr
    exact ⟨Nat.eq_of_beq_eq_true hr.2.1, hr.2.2.1, beq_iff_eq.1 hr.2.2.2⟩

theorem groups_inv (hJ : ∀ j < 75, vlJK j = true) (hE : ∀ t < 32, etaCK t = true)
    (hS : ∀ t < 256, segK t = true) (hP : ∀ p < 1980, pairAtK p = true) :
    GInv 1980 vlGroups := by
  have hl : vlPairs.length = 1980 := by rw [vlPairs_eq hJ hE hS, List.length_map, ql_len]
  have h := fold_inv (P := vlPairs) (Inv := GInv)
    (F := fun acc p => if acc.any (fun G => G.any (eqRows (vlT p))) then acc else acc ++ [vlGroupOf (vlT p)])
    ⟨by rw [vlc0]; rfl, fun h hh => by rw [vlc0] at hh; omega⟩ ?_ 1980 (by omega)
  · rw [← hl, List.take_length] at h
    rw [← hl]
    exact h
  · intro p hp acc hI
    have hp1 : p < 1980 := hl ▸ hp
    have hT := pair_enc hJ hE hS hp
    obtain ⟨-, -, -, hold, hnew⟩ := pairAt_parts (hP p hp1)
    rw [any_acc hI hT]
    cases hb : Nat.beq (getN 0 VLN p) 1
    · obtain ⟨hlt, hc, hin⟩ := hold hb
      have ha : (List.range (getN 0 VLC p)).any (fun h => (grpK h).any (Nat.beq (tKp p))) = true :=
        List.any_eq_true.2 ⟨_, List.mem_range.2 hlt, hin⟩
      rw [ha]
      simp only [↓reduceIte]
      exact ⟨hI.1.trans hc.symm, fun h hh => hI.2 h (hc ▸ hh)⟩
    · obtain ⟨hc, ha, hg⟩ := hnew hb
      rw [ha]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hG := group_enc hT
      refine ⟨by rw [List.length_append, hI.1, hc]; rfl, fun h hh => ?_⟩
      rw [hc] at hh
      rcases Nat.lt_succ_iff_lt_or_eq.1 hh with hh | rfl
      · rw [List.getD_append _ _ _ _ (by rw [hI.1]; exact hh)]
        exact hI.2 h hh
      · rw [List.getD_append_right _ _ _ _ (by rw [hI.1]), hI.1, Nat.sub_self]
        exact ⟨hG.1, hG.2.trans hg⟩

theorem distinct_of {T : Array V2} {t : Nat} (hT : WfA T ∧ encR T = t) (hd : distK (gK t) = true) :
    vlDistinct (vlGroupOf T) = true := by
  have hG := group_enc hT
  have hlen : (vlGroupOf T).length = 16 := by simp [vlGroupOf]
  have hget : ∀ i < 16, getN one (gK t) i = encR ((vlGroupOf T).getD i #[]) := fun i hi => by
    rw [getN_eq_getD, ← hG.2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem (by omega)]
    rfl
  have hw : ∀ i < 16, WfA ((vlGroupOf T).getD i #[]) := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hG.1 _ (List.getElem_mem _)
  unfold vlDistinct
  rw [hlen, Bool.and_eq_true]
  refine ⟨rfl, List.all_eq_true.2 fun i hi => List.all_eq_true.2 fun j hj => ?_⟩
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  have k := allR_spec (allR_spec hd i hi') j hj'
  rw [hget i hi', hget j (by omega), notB_eq] at k
  rw [eqRows_of ⟨hw i hi', rfl⟩ ⟨hw j (by omega), rfl⟩]
  exact k

theorem groups_ok (hJ : ∀ j < 75, vlJK j = true) (hE : ∀ t < 32, etaCK t = true)
    (hS : ∀ t < 256, segK t = true) (hP : ∀ p < 1980, pairAtK p = true) : chkVlGroups = true := by
  have hl : vlPairs.length = 1980 := by rw [vlPairs_eq hJ hE hS, List.length_map, ql_len]
  have hI := groups_inv hJ hE hS hP
  unfold chkVlGroups
  simp only [Bool.and_eq_true]
  refine ⟨⟨by simp [hl], by simp [hI.1, vlc1980]⟩, ?_⟩
  refine List.all_eq_true.2 fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hx
  have hp1 : p < 1980 := hl ▸ hp
  have hT := pair_enc hJ hE hS hp
  obtain ⟨hd, hh, hall, -, -⟩ := pairAt_parts (hP p hp1)
  have hG := group_enc hT
  rw [Bool.and_eq_true]
  refine ⟨distinct_of hT hd, ?_⟩
  have hh' : getN 0 VLH p < vlGroups.length := by rw [hI.1, vlc1980]; exact hh
  have hgi := hI.2 (getN 0 VLH p) (by rw [vlc1980]; exact hh)
  refine List.any_eq_true.2 ⟨vlGroups.getD (getN 0 VLH p) [], ?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh', Option.getD_some]
    exact List.getElem_mem _
  · refine List.all_eq_true.2 fun M hM => ?_
    rw [any_grp ⟨hG.1 M hM, rfl⟩ hgi.1, hgi.2]
    rw [← hG.2] at hall
    exact List.all_eq_true.1 hall (encR M) (List.mem_map_of_mem hM)

theorem lifts_ok (hJ : ∀ j < 75, vlJK j = true) : chkVlLifts = true := by
  unfold chkVlLifts
  rw [vlTables_eq, Bool.and_eq_true]
  refine ⟨by simp, List.all_eq_true.2 fun y hy => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
  have hj' := List.mem_range.1 hj
  obtain ⟨h1, h2, -⟩ := vlJ_of (hJ j hj')
  rw [vlLiftWord_eq (vli_lt hj'), Bool.and_eq_true]
  exact ⟨h1, h2⟩

theorem liftWf_ok : chkVlLiftWf = true := by
  unfold chkVlLiftWf
  refine List.all_eq_true.2 fun y hy => ?_
  rw [liftRows_eq hy, Bool.and_eq_true]
  have h := wR_enc (vlLiftWord y)
  refine ⟨wf_bool h.1, ?_⟩
  rw [eqRows_of h h]
  exact Nat.beq_refl _

theorem eta_ok : chkVlEta = true := by
  unfold chkVlEta
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by simp [vlEtaTab], ?_⟩, wf_bool wf_idRows⟩
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 2048 := by simpa [vlEtaTab] using hi
  have e : vlEtaTab[i] = etaE i := by
    rw [← getElem!_pos vlEtaTab i hi]
    exact vlEta_get hi'
  rw [e]
  exact wf_bool (etaE_enc i).1

theorem vlLines_ok : chkVlLines = true := by
  unfold chkVlLines
  rw [lines17_eq]
  simp [L17]

theorem vlAll_of (hJ : ∀ j < 75, vlJK j = true) (hE : ∀ t < 32, etaCK t = true)
    (hS : ∀ t < 256, segK t = true) (hP : ∀ p < 1980, pairAtK p = true) : chkVlAll = true := by
  unfold chkVlAll
  rw [lifts_ok hJ, liftWf_ok, eta_ok, groups_ok hJ hE hS hP, vlLines_ok]
  rfl

end CertificateChecks.KernelJ4Q

end

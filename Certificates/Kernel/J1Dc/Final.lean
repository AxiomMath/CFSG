
module

public import Certificates.Kernel.J1Dc.Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatOfFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.Prim

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J1Dc

open CFSG.KC.SLDc CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB
open CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Sporadic.J1 CFSG.Quasithin.A312S.J1

@[expose] noncomputable def j1LatK : LatData (List ℕ) where
  O := default
  F := default
  sTabs := j1STabs
  mw := J.mw.toArray
  mt := J.mw.toArray.map fun ws => ws.map (wordTabA #[j1ta.toArray, j1tb.toArray] 1540)
  Om := #[Om 0, Om 1, Om 2, Om 3, Om 4, Om 5, Om 6, Om 7, Om 8, Om 9, Om 10, Om 11, Om 12, Om 13,
    Om 14, Om 15, Om 16]
  atoms := #[]
  joins := []

theorem mw_len : J.mw.length = 17 := rfl

theorem mw_size : j1LatK.mw.size = 17 := rfl

theorem mw_get (j : ℕ) : j1LatK.mw[j]! = J.mw.getD j [] := by
  change J.mw.toArray[j]! = _
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem mt_get {j : ℕ} (hj : j < 17) :
    j1LatK.mt[j]! = (j1LatK.mw[j]!).map (wordTabA #[j1ta.toArray, j1tb.toArray] 1540) := by
  change (J.mw.toArray.map _)[j]! = (J.mw.toArray[j]!).map _
  rw [getElem!_pos _ j (by simp [mw_len, hj]), getElem!_pos J.mw.toArray j (by simp [mw_len, hj])]
  simp

theorem Om_get {j : ℕ} (hj : j < 17) : j1LatK.Om[j]! = Om j := by
  interval_cases j <;> rfl

theorem mwB : (J.mw.all fun ws => ws.all fun w => w.all (· < 2)) = true := by quickRfl

theorem mw_lt2 {j : ℕ} : ∀ w ∈ J.mw.getD j [], ∀ l ∈ w, l < 2 := by
  intro w hw l hl
  rcases Nat.lt_or_ge j J.mw.length with hj | hj
  · rw [List.getD_eq_getElem _ _ hj] at hw
    have h1 := List.all_eq_true.1 mwB _ (List.getElem_mem hj)
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 w hw) l hl
    simpa using h2
  · rw [List.getD_eq_default _ _ hj] at hw
    simp at hw

theorem ptAct_good {t : Array ℕ} {f : ℕ → ℕ} (h : Good 1540 t f) {x : List ℕ}
    (hx : ∀ p ∈ x, p < 1540) : ptAct t x = labF f x ∧ ∀ q ∈ labF f x, q < 1540 := by
  have e : x.map (fun p => t.getD p 0) = x.map f :=
    List.map_congr_left fun p hp => (h.2 p (hx p hp)).1
  have e2 : ptAct t x = labF f x := by
    unfold ptAct labF
    rw [e, sortN_eq]
  refine ⟨e2, fun q hq => ?_⟩
  unfold labF at hq
  rw [← sortN_eq, mem_sortN] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  exact (h.2 p (hx p hp)).2

theorem mf_lt {j l : ℕ} (hl : l < 3) : mf j l = L2 l := by
  have h : Nat.blt l 3 = true := by simpa [Nat.blt_eq] using hl
  unfold mf
  rw [h]
  rfl

theorem mf_ge {j k : ℕ} : mf j (3 + k) = wordF L ((J.mw.getD j []).getD k []) := by
  have h : Nat.blt (3 + k) 3 = false := by
    rw [Bool.eq_false_iff]
    intro h'
    rw [Nat.blt_eq] at h'
    omega
  unfold mf
  rw [h]
  change wordF L ((J.mw.getD j []).getD (3 + k - 3) []) = _
  rw [Nat.add_sub_cancel_left]

theorem toArray_get! (X : List (Array ℕ)) (l : ℕ) : X.toArray[l]! = X.getD l #[] := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getD_eq_getElem?_getD]
  rfl

theorem j1STabs_eq : j1STabs = genTabs 1540 sgK := sgK_tabs.symm

theorem letters_eq {j : ℕ} (hj : j < 17) : j1LatK.sTabs ++ j1LatK.mt[j]! =
    genTabs 1540 sgK ++ (J.mw.getD j []).map (wordTabA #[j1ta.toArray, j1tb.toArray] 1540) := by
  rw [mt_get hj, mw_get]
  change j1STabs ++ _ = _
  rw [j1STabs_eq]

theorem letters_size {j : ℕ} (hj : j < 17) :
    (j1LatK.sTabs ++ j1LatK.mt[j]!).toArray.size = Nat.add 3 (J.mw.getD j []).length := by
  rw [letters_eq hj, List.size_toArray, List.length_append, List.length_map, genTabs,
    List.length_map, sgK_len]
  rfl

theorem good_letter {j : ℕ} (hj : j < 17) {l : ℕ}
    (hl : l < (j1LatK.sTabs ++ j1LatK.mt[j]!).toArray.size) :
    Good 1540 (j1LatK.sTabs ++ j1LatK.mt[j]!).toArray[l]! (mf j l) := by
  have hl' : l < 3 + (J.mw.getD j []).length := by
    rw [letters_size hj] at hl
    exact hl
  rw [toArray_get!, letters_eq hj]
  have hg3 : (genTabs 1540 sgK).length = 3 := by rw [genTabs, List.length_map, sgK_len]
  rcases Nat.lt_or_ge l 3 with h3 | h3
  · rw [List.getD_append _ _ _ _ (by rw [hg3]; exact h3), mf_lt h3]
    have e : (genTabs 1540 sgK).getD l #[] = (genTabs 1540 sgK).toArray.getD l #[] := by
      rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    rw [e, genTabs_hel sgK l (by simpa [sgK_len] using h3)]
    have e2 : sgK.toArray.getD l 1 = sgK.getD l 1 := by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [e2]
    exact good_sg h3
  · obtain ⟨k, rfl⟩ : ∃ k, l = 3 + k := ⟨l - 3, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by rw [hg3]; omega), hg3, Nat.add_sub_cancel_left, mf_ge]
    have hk : k < (J.mw.getD j []).length := by omega
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]
    have hw : (J.mw.getD j [])[k] ∈ J.mw.getD j [] := List.getElem_mem hk
    have h := good_word good_ab (by simpa using mw_lt2 _ hw)
    rw [List.getD_eq_getElem _ _ hk]
    exact h

theorem j1K_membersOK :
    MembersOK ptAct 1540 j1ta.toArray j1tb.toArray j1Delta j1LatK := by
  refine ⟨by rw [mw_size]; decide, by rw [mw_get]; rfl, by simp [j1LatK], rfl, fun j hj => ?_⟩
  have hj' : j < 17 := hj
  refine ⟨by rw [mw_get]; exact mw_lt2, by rw [mt_get hj'], ?_⟩
  rw [Om_get hj']
  have hsz := letters_size hj'
  have hm := M.all j hj'
  unfold memOK at hm
  rw [← hsz, eq_of_beq deltaB] at hm
  refine (omOKG_sound (act := ptAct) (P := fun x => ∀ p ∈ x, p < 1540)
    (fun p hp => (j1_delta_valid).2 p hp) (fun l hl x hx => ?_) hm).1
  obtain ⟨e, hlt⟩ := ptAct_good (good_letter hj' hl) hx
  exact ⟨hlt, e⟩

theorem j1K_comp : ∀ Z : Subgroup G, Subgroup.closure {x | x ∈ sgK} ≤ Z →
    ∃ j ≤ j1LatK.mw.size, Z = memberOrTop j1LatK.mw.size
      (fun j => Subgroup.closure
        {x | x ∈ sgK ++ (j1LatK.mw[j]!).map (wordElt (a : G) (b : G))}) j := by
  intro Z hZ
  obtain ⟨j, hj, e⟩ := dc_complete Z hZ
  refine ⟨j, by rw [mw_size]; rw [mw_len] at hj; exact hj, ?_⟩
  rw [e, mw_size, ← mw_len]
  simp only [mw_get]

@[expose] noncomputable def j1CtxK : LatCtx G 1540 (List ℕ) :=
  LatCtx.ofFacts ptLab (PtValid 1540) ptLab_lawful j1Delta j1_delta_valid (a : G) (b : G)
    j1ta.toArray j1tb.toArray j1_tab_a j1_tab_b closure_ab j1LatK sgK 3 sgK_tabs j1K_card_S
    21945 (by rw [card_J]; norm_num) j1K_membersOK j1K_stab j1K_comp

theorem j1K_D_mw : j1CtxK.D.mw = j1LatK.mw := rfl

theorem j1K_D_Om : j1CtxK.D.Om = j1LatK.Om := rfl

theorem j1K_J : j1CtxK.J = 17 := by
  unfold LatCtx.J
  rw [j1K_D_mw, mw_size]

theorem j1K_S : j1CtxK.S = Subgroup.closure {x | x ∈ sgK} := j1CtxK.hSeq.symm

@[expose] def szs : List ℕ := [1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21]

theorem szB : ((List.range 17).map (fun j => (Om j).lbl.size) == szs) = true := by quickRfl

theorem sz_get {j : ℕ} (hj : j < 17) : (Om j).lbl.size = szs.getD j 0 := by
  have e := congrArg (fun l => l.getD j 0) (eq_of_beq szB)
  rw [← e, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

theorem j1K_card {j : ℕ} (hj : j < 17) : Nat.card (j1CtxK.Y j) = szs.getD j 0 * 2 ^ 3 := by
  rw [j1CtxK.Y_card (by rw [j1K_J]; exact hj), j1K_D_Om, Om_get hj, sz_get hj]
  rfl

theorem j1K_gens {j : ℕ} {g : G} (hg : g ∈ j1CtxK.sg ++ j1CtxK.gens j) :
    (∃ i < 3, g = sgK.getD i 1) ∨
      ∃ k < (J.mw.getD j []).length, g = wordElt (a : G) (b : G) ((J.mw.getD j []).getD k []) := by
  rcases List.mem_append.1 hg with h | h
  · left
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
    have hi3 : i < 3 := by
      have : j1CtxK.sg = sgK := rfl
      rw [this, sgK_len] at hi
      exact hi
    exact ⟨i, hi3, by rw [List.getD_eq_getElem _ _ (by rw [sgK_len]; exact hi3)]; rfl⟩
  · right
    have e : j1CtxK.gens j = (J.mw.getD j []).map (wordElt (a : G) (b : G)) := by
      unfold LatCtx.gens
      rw [j1K_D_mw, mw_get]
      rfl
    rw [e] at h
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem good_gen {j : ℕ} {g : G} (hg : g ∈ j1CtxK.sg ++ j1CtxK.gens j) :
    ∃ l < Nat.add 3 (J.mw.getD j []).length, Good 1540 (tab 1540 g).toArray (mf j l) := by
  rcases j1K_gens hg with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩
  · exact ⟨i, by change i < 3 + _; omega, by rw [mf_lt hi]; exact good_sg hi⟩
  · refine ⟨3 + k, by change 3 + k < 3 + _; omega, ?_⟩
    rw [mf_ge]
    have hw : (J.mw.getD j []).getD k [] ∈ J.mw.getD j [] := by
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    exact good_wordElt (mw_lt2 _ hw)

theorem lab_good {g : G} {f : ℕ → ℕ} (hg : Good 1540 (tab 1540 g).toArray f) :
    lab 1540 ptLab j1Delta g = labF f j1Delta ∧ ∀ q ∈ labF f j1Delta, q < 1540 :=
  ptAct_good hg fun p hp => j1_delta_valid.2 p hp

theorem j1K_norm16 :
    j1CtxK.Y 16 ≤ Subgroup.normalizer ((Subgroup.closure {x | x ∈ sgK} : Subgroup G) : Set G) := by
  set S : Subgroup G := Subgroup.closure {x | x ∈ sgK} with hSdef
  rw [LatCtx.Y, Subgroup.closure_le]
  intro g hg
  rcases j1K_gens hg with ⟨i, hi, rfl⟩ | ⟨k, hk, rfl⟩
  · exact Subgroup.le_normalizer (Subgroup.subset_closure (by
      rw [List.getD_eq_getElem _ _ (by rw [sgK_len]; exact hi)]
      exact List.getElem_mem _))
  · set w := (J.mw.getD 16 []).getD k [] with hwdef
    set g := wordElt (a : G) (b : G) w with hgdef
    have hw : w ∈ J.mw.getD 16 [] := by
      rw [hwdef, List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    have hgg := good_wordElt (mw_lt2 _ hw)
    obtain ⟨eg, hlt⟩ := lab_good hgg
    have hconj : ∀ s ∈ sgK, g⁻¹ * s * g ∈ S := by
      intro s hs
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
      have hi3 : i < 3 := by rwa [sgK_len] at hi
      have hn := List.all_eq_true.1 (List.all_eq_true.1 normB w hw) i (List.mem_range.2 hi3)
      rw [eq_of_beq deltaB] at hn
      have h1 : ptAct (tab 1540 (sgK.getD i 1)).toArray (lab 1540 ptLab j1Delta g) =
          lab 1540 ptLab j1Delta g := by
        rw [eg, (ptAct_good (good_sg hi3) hlt).1]
        exact beq_iff_eq.1 hn
      have h2 : lab 1540 ptLab j1Delta g = lab 1540 ptLab j1Delta (sgK.getD i 1 * g) := by
        rw [lab_mul ptLab_lawful j1_delta_valid]
        exact h1.symm
      have h3 := (lab_eq_iff ptLab_lawful j1_delta_valid g (sgK.getD i 1 * g)).mp h2
      rw [mem_stab, j1K_stab, ← mul_assoc] at h3
      rw [List.getD_eq_getElem _ _ hi] at h3
      exact h3
    have hle : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
      rw [hSdef, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨s, hs, rfl⟩
      have := hconj s hs
      simpa [MulAut.conj_apply] using this
    have heq : S.map (MulAut.conj g⁻¹).toMonoidHom = S :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective])
    have : g⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
    simpa using Subgroup.inv_mem _ this

theorem one_good : Good 1540 (tab 1540 (1 : G)).toArray (fun p => p) := by
  refine ⟨by simp [tab], fun p hp => ⟨?_, hp⟩⟩
  have e := img_tab (n := 1540) (1 : G) p
  rw [img] at e
  rw [e, act_one hp]

theorem centWords_lt : ∀ p ∈ j1CentWords, ∀ l ∈ p.2, l < 3 := by decide

theorem j1K_cent {j : ℕ} {w : List ℕ} (hjw : (j, w) ∈ j1CentWords) :
    ∃ u ∈ Subgroup.closure {x | x ∈ sgK}, orderOf u = 2 ∧
      j1CtxK.Y j ≤ Subgroup.centralizer ({u} : Set G) := by
  have hw : ∀ l ∈ w, l < 3 := centWords_lt _ hjw
  have hc := List.all_eq_true.1 centB _ hjw
  unfold centOK at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, List.mem_range,
    Bool.not_eq_true', beq_eq_false_iff_ne] at hc
  obtain ⟨hall, q0, hq0, hne⟩ := hc
  have gu := good_sw hw
  refine ⟨sElt w, sElt_mem hw, ?_, ?_⟩
  · have hu1 : sElt w ≠ 1 := by
      intro h
      apply hne
      have e := (act_of_good gu hq0).1
      rw [h, act_one hq0] at e
      exact e.symm
    have hu2 : sElt w * sElt w = 1 :=
      eq_of_maps (good_mul' gu gu) one_good fun p hp => (hall p hp).1
    exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  · rw [LatCtx.Y, Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨l, hl, gg⟩ := good_gen hg
    exact eq_of_maps (good_mul' gg gu) (good_mul' gu gg) fun p hp => (hall p hp).2 l hl

theorem sz120 : ∀ j < 17, szs.getD j 0 = 15 → (j, (j1CentWords.lookup j).getD []) ∈ j1CentWords := by
  decide

theorem sz168 : ∀ j < 17, szs.getD j 0 = 21 → j = 16 := by decide

theorem j1K_facts (Z : Subgroup G) (hZ : Subgroup.closure {x | x ∈ sgK} ≤ Z) :
    (Nat.card Z = 168 →
      Z ≤ Subgroup.normalizer ((Subgroup.closure {x | x ∈ sgK} : Subgroup G) : Set G)) ∧
    (Nat.card Z = 120 → ∃ u ∈ Subgroup.closure {x | x ∈ sgK}, orderOf u = 2 ∧
      Z ≤ Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨j, hj, rfl⟩ := j1CtxK.complete Z (by rw [j1K_S]; exact hZ)
  rw [j1K_J] at hj ⊢
  by_cases hj17 : j < 17
  · have e : memberOrTop 17 j1CtxK.Y j = j1CtxK.Y j := by
      unfold memberOrTop
      rw [if_pos hj17]
    rw [e, j1K_card hj17]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h16 := sz168 j hj17 (by omega)
      subst h16
      exact j1K_norm16
    · exact j1K_cent (sz120 j hj17 (by omega))
  · have e : memberOrTop 17 j1CtxK.Y j = ⊤ := by
      unfold memberOrTop
      rw [if_neg hj17]
    rw [e, Subgroup.card_top, card_J]
    exact ⟨fun h => absurd h (by norm_num), fun h => absurd h (by norm_num)⟩

end CFSG.KD.J1Dc

end

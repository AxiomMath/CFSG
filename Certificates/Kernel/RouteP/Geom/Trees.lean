module

public import Certificates.Kernel.RouteP.Geom.Check
public import Certificates.Kernel.RouteP.Obj.Glue
public import CFSG.Certificates.Kernel.RouteP.GeomSound
public import Certificates.Data.RouteP.Geom

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native CFSG.Perm.Native
  CFSG.KC.Benes CFSG.KS.Fi24Net

noncomputable abbrev gS (i : Nat) : Nat := zS NWP KAP KBP zpL i

noncomputable abbrev gA : Nat := closeS NWO KAO KBO [-7, -8, -9] 10 (single 99705)

@[expose] def a1L : List Int := [-7, -8, -9]

theorem gFacts : GeomCoreFacts NWP KAP KBP NWO KAO KBO zpL [-7, -8, -9]
    (sel7 (gS 0) (gS 1) (gS 2) (gS 3) (gS 4) (gS 5) (gS 6)) gA :=
  geomSetOK_spec GeomCk.geomSet

theorem gsel {i : Nat} (hi : i < 7) : sel7 (gS 0) (gS 1) (gS 2) (gS 3) (gS 4) (gS 5) (gS 6) i = gS i :=
  sel7_eq gS hi

theorem gRoot_lt {i : Nat} (hi : i < 7) : gRoot i < 920808 := by interval_cases i <;> decide

theorem geomReps_get {i : Nat} (hi : i < 7) : geomReps[i]! = gRoot i := by interval_cases i <;> rfl

theorem geomSizes_get {i : Nat} (hi : i < 7) : geomSizes[i]! = gSize i := by interval_cases i <;> rfl

theorem geomLevels_get {i : Nat} (hi : i < 7) : geomLevels[i]! = gLev i := by interval_cases i <;> rfl

theorem andB_of {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

theorem gOrb {i : Nat} (hi : i < 7) : orbOK NWP KAP KBP zpL (gRoot i) (gRounds i) (gSize i) = true := by
  unfold orbOK
  rw [letB_eq']
  have h1 := gFacts.closed i hi
  have h2 := gFacts.count i hi
  rw [gsel hi] at h1 h2
  have h2' : pcount (Nat.land (closeS NWP KAP KBP zpL (gRounds i) (single (gRoot i))) ptsS) =
      gSize i := h2
  exact andB_of h1 (by rw [h2']; exact Nat.beq_refl _)

theorem aOrb : orbOK NWO KAO KBO [-7, -8, -9] 99705 10 3510 = true := by
  unfold orbOK
  rw [letB_eq']
  exact andB_of gFacts.a_closed (by rw [gFacts.a_count]; exact Nat.beq_refl _)

theorem hzl : ∀ l ∈ zpLetters, l < 22 := by decide

theorem hapZ : ∀ l ∈ zpLetters, ∀ x < 920808,
    ap (genTabs ())[l]! x = eL NWP KAP KBP (cq ((l + 1 : Nat) : ℤ)) x := by
  intro l hl x hx
  rw [ap_genTabs mTabs_P (hzl l hl) hx]
  exact (gq_act (hzl l hl) ⟨x, hx⟩).1

theorem hzL : zpL = zpLetters.toList.map fun l => cq ((l + 1 : Nat) : ℤ) := by decide

theorem hgZ : ∀ z ∈ zpL, LOK NWP KAP KBP z := by
  intro z hz
  simp only [zpL, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact lokP (by decide)

theorem gTree {i : Nat} (hi : i < 7) :
    (treeBFS degree (gRoot i) (genTabs ()) zpLetters).pts.size = gSize i ∧
      treeOK degree (gRoot i) (treeBFS degree (gRoot i) (genTabs ()) zpLetters) (genTabs ()) zpLetters = true ∧
      ∀ x < 920808, (∃ j < (treeBFS degree (gRoot i) (genTabs ()) zpLetters).pts.size,
        ap (treeBFS degree (gRoot i) (genTabs ()) zpLetters).pts j = x) ↔ memS (gS i) x = true :=
  tree_of_orbOK (gRoot_lt hi) hzL hgZ hapZ (fun l hl => by have := hzl l hl; omega) (gOrb hi)

theorem hapA : ∀ l ∈ geomA1Letters, ∀ x < 920808,
    ap (objRun ()).1[l]! x = eL NWO KAO KBO (Int.negSucc l) x := by
  intro l hl x hx
  have hl' : l < 58 := by simp [geomA1Letters] at hl; omega
  rw [objRun_rep l hl' x hx, idx_of_lt _ hx, Perm.smul_def]
  exact gT_apply (lokO_reg hl') ⟨x, hx⟩

theorem aTree :
    (treeBFS degree 99705 (objRun ()).1 geomA1Letters).pts.size = 3510 ∧
      treeOK degree 99705 (treeBFS degree 99705 (objRun ()).1 geomA1Letters) (objRun ()).1
        geomA1Letters = true ∧
      ∀ x < 920808, (∃ j < (treeBFS degree 99705 (objRun ()).1 geomA1Letters).pts.size,
        ap (treeBFS degree 99705 (objRun ()).1 geomA1Letters).pts j = x) ↔ memS gA x = true :=
  tree_of_orbOK (c := Int.negSucc) (by decide) (by decide)
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> exact lokO (by decide))
    hapA (fun l hl => by simp [geomA1Letters] at hl; omega) aOrb

theorem memTree_iff {n r : Nat} {T : Tree} {letters : Array Table} {lv : Array Nat}
    (h : treeOK n r T letters lv = true) (x : Nat) :
    memTree T x = true ↔ ∃ j < T.pts.size, ap T.pts j = x := by
  constructor
  · intro hm
    simp only [memTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
    exact ⟨ap T.pos x, hm.1, hm.2⟩
  · rintro ⟨j, hj, rfl⟩
    simp only [CFSG.Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    have hat := (allIn_eq_true.1 h.2) j (Nat.zero_le _) hj
    simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hat
    simp only [memTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    rw [hat.1.1.2]
    exact ⟨hj, rfl⟩

theorem pts_lt_of_treeOK {n r : Nat} {T : Tree} {letters : Array Table} {lv : Array Nat}
    (h : treeOK n r T letters lv = true) {j : Nat} (hj : j < T.pts.size) : ap T.pts j < n := by
  simp only [CFSG.Perm.Native.treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  have hat := (allIn_eq_true.1 h.2) j (Nat.zero_le _) hj
  simp only [treeAt, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hat
  exact hat.1.1.1

theorem geomTrees_size :(geomTrees (genTabs ())).size = 7 := by simp [geomTrees, geomReps]

theorem geomTrees_get {i : Nat} (hi : i < 7) :
    (geomTrees (genTabs ()))[i]! = treeBFS degree (gRoot i) (genTabs ()) zpLetters := by
  unfold geomTrees
  rw [getElem!_pos _ i (by simp [geomReps]; omega), Array.getElem_map, ← geomReps_get hi,
    getElem!_pos geomReps i (by simp [geomReps]; omega)]

theorem mem_gTree_iff {i : Nat} (hi : i < 7) {x : Nat} (hx : x < 920808) :
    memTree (geomTrees (genTabs ()))[i]! x = memS (gS i) x := by
  rw [geomTrees_get hi, Bool.eq_iff_iff, memTree_iff (gTree hi).2.1, (gTree hi).2.2 x hx]

theorem exists_gS (x : Nat) (hx : x < 920808) : ∃ i < 7, memS (gS i) x = true := by
  obtain ⟨i, hi, h⟩ := cover_memS gFacts.cover hx
  exact ⟨i, hi, by rwa [gsel hi] at h⟩

theorem gS_unique {i j : Nat} (hi : i < 7) (hj : j < 7) {x : Nat} (h1 : memS (gS i) x = true)
    (h2 : memS (gS j) x = true) : i = j := by
  by_contra hij
  have := gFacts.disj i hi j hj hij
  rw [gsel hi, gsel hj] at this
  exact disj_memS this x ⟨h1, h2⟩

theorem firstTree_eq (trees : Array Tree) (v : Nat) :
    firstTree trees v = if memTree trees[0]! v then 0 else if memTree trees[1]! v then 1 else
      if memTree trees[2]! v then 2 else if memTree trees[3]! v then 3 else
      if memTree trees[4]! v then 4 else if memTree trees[5]! v then 5 else
      if memTree trees[6]! v then 6 else 7 := by
  unfold firstTree
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [List.range', List.forIn_cons, List.forIn_nil]
  cases memTree trees[0]! v <;> cases memTree trees[1]! v <;> cases memTree trees[2]! v <;>
    cases memTree trees[3]! v <;> cases memTree trees[4]! v <;> cases memTree trees[5]! v <;>
    cases memTree trees[6]! v <;> rfl

theorem firstTree_of {i : Nat} (hi : i < 7) {x : Nat} (hx : x < 920808) (h : memS (gS i) x = true) :
    firstTree (geomTrees (genTabs ())) x = i := by
  have hm : ∀ j < 7, memTree (geomTrees (genTabs ()))[j]! x = decide (j = i) := by
    intro j hj
    rw [mem_gTree_iff hj hx]
    by_cases e : j = i
    · subst e
      rw [h, decide_eq_true rfl]
    · rw [decide_eq_false e]
      cases hj' : memS (gS j) x
      · rfl
      · exact absurd (gS_unique hj hi hj' h) e
  rw [firstTree_eq, hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide),
    hm 4 (by decide), hm 5 (by decide), hm 6 (by decide)]
  interval_cases i <;> rfl

theorem ap_geomLab {i : Nat} (hi : i < 7) {x : Nat} (hx : x < 920808) (h : memS (gS i) x = true) :
    ap (geomLab (geomTrees (genTabs ()))) x = i := by
  unfold geomLab
  rw [ap_ofFn _ hx]
  simp only
  rw [firstTree_of hi hx h, toNat_ofNat_lt' (by omega)]

theorem root_mem {i : Nat} (hi : i < 7) : memS (gS i) (gRoot i) = true :=
  (orb_spec (gRoot_lt hi) hgZ (gOrb hi)).1

theorem closed_mem {i : Nat} (hi : i < 7) {x : Nat} (hx : x < 920808) (h : memS (gS i) x = true)
    {l : Nat} (hl : l ∈ zpLetters) : memS (gS i) (ap (genTabs ())[l]! x) = true := by
  rw [hapZ l hl x hx]
  exact (orb_spec (gRoot_lt hi) hgZ (gOrb hi)).2.1 x hx h _
    (by rw [hzL]; exact List.mem_map.2 ⟨l, by simpa using hl, rfl⟩)

theorem zpTreesOK_true : zpTreesOK (genTabs ()) (geomTrees (genTabs ())) = true := by
  unfold zpTreesOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨geomTrees_size, allIn_eq_true.2 fun i _ hi => ?_⟩
  rw [geomTrees_get hi, geomSizes_get hi, geomReps_get hi, (gTree hi).1, beq_self_eq_true,
    Bool.true_and]
  exact (gTree hi).2.1

theorem labOK_true :
    labOK (genTabs ()) (geomTrees (genTabs ())) (geomLab (geomTrees (genTabs ()))) = true := by
  unfold labOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨allIn_eq_true.2 fun i _ hi => ?_, allIn_eq_true.2 fun v _ hv => ?_⟩, ?_⟩
  · rw [beq_iff_eq, geomReps_get hi]
    exact ap_geomLab hi (gRoot_lt hi) (root_mem hi)
  · obtain ⟨i, hi, h⟩ := exists_gS v hv
    rw [ap_geomLab hi hv h]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hi, by rw [mem_gTree_iff hi hv]; exact h⟩
  · rw [Array.all_eq_true]
    intro j hj
    rw [allIn_eq_true]
    intro v _ hv
    have hl : zpLetters[j] ∈ zpLetters := Array.getElem_mem hj
    obtain ⟨i, hi, h⟩ := exists_gS v hv
    have hgv : ap (genTabs ())[zpLetters[j]]! v < 920808 := by
      rw [hapZ _ hl v hv]
      exact eL_lt (hgZ _ (by rw [hzL]; exact List.mem_map.2 ⟨_, by simpa using hl, rfl⟩)) hv
    rw [beq_iff_eq, ap_geomLab hi hgv (closed_mem hi hv h hl), ap_geomLab hi hv h]

theorem memS_land (a b N : Nat) : memS (Nat.land a b) N = (memS a N && memS b N) := by
  unfold memS
  change (a &&& b).testBit _ = _
  rw [Nat.testBit_and]

theorem s1OK_true :
    s1OK (objRun ()).1 (geomTrees (genTabs ())) (treeBFS degree 99705 (objRun ()).1 geomA1Letters) =
      true := by
  have hpt : ∀ {r x y : Nat}, r < 58 → x < 920808 → y < 920808 →
      ptOK NWO KAO KBO [((r + 1 : Nat) : ℤ)] x y = true → ap (objRun ()).1[r]! y = x :=
    fun hr hx hy h => ap_of_ptOK (objRun_rep _ hr) (lokO_reg hr) hx hy h
  unfold s1OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨?_, aTree.1⟩, aTree.2.1⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro j hj
    have hj3 : j < 3 := by simpa [geomA1Letters] using hj
    have e : geomA1Letters[j] = j + 6 := by interval_cases j <;> rfl
    have e' : j + 7 = geomA1Letters[j] + 1 := by rw [e]
    have h0 := gFacts.fix0 j hj3
    have h1 := gFacts.fix1 j hj3
    rw [e'] at h0 h1
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hpt (by omega) (by decide) (by decide) h0, hpt (by omega) (by decide) (by decide) h1⟩
  · rw [Array.all_eq_true]
    intro j hj
    have hok := (gTree (i := 1) (by decide)).2.1
    have hS1 := (gTree (i := 1) (by decide)).2.2
    rw [← geomTrees_get (i := 1) (by decide)] at hS1 hok
    set T := (geomTrees (genTabs ()))[1]!
    have hc : ap T.pts j = (T.pts[j]).toNat := by simp only [ap, getElem!_pos T.pts j hj]
    have hclt : (T.pts[j]).toNat < 920808 := hc ▸ pts_lt_of_treeOK hok hj
    have hcS : memS (gS 1) (T.pts[j]).toNat = true := (hS1 _ hclt).1 ⟨j, hj, hc⟩
    set c := (T.pts[j]).toNat
    have hw : ap (objRun ()).1[tauReg]! c = eL NWO KAO KBO (-10) c := by
      rw [objRun_rep tauReg (by decide) c hclt, idx_of_lt _ hclt, Perm.smul_def]
      exact gT_apply (lokO_reg (r := 9) (by decide)) ⟨c, hclt⟩
    have hl10 : LOK NWO KAO KBO (-10) := lokO (by decide)
    have hwlt : eL NWO KAO KBO (-10) c < 920808 := eL_lt hl10 hclt
    simp only [hw, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    by_cases hm : memTree T (eL NWO KAO KBO (-10) c) = true
    · right
      have hm' : memS (gS 1) (eL NWO KAO KBO (-10) c) = true := by
        rw [← mem_gTree_iff (i := 1) (by decide) hwlt]
        exact hm
      have hX : memS (Nat.land (imgS NWO KAO KBO (-10) (gS 1)) (gS 1))
          (eL NWO KAO KBO (-10) c) = true := by
        rw [memS_land, memS_imgS hl10 _ hclt, hcS, hm']
        rfl
      have ht := gFacts.tau
      rw [gsel (i := 1) (by decide)] at ht
      rw [← ht, memS_land, Bool.and_eq_true] at hX
      rw [memTree_iff aTree.2.1, aTree.2.2 _ hwlt]
      exact hX.2
    · left
      simpa using hm

end CertificateChecks.KernelRouteP

end

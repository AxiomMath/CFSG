module

public import Certificates.Kernel.RouteP.Geom.Trees
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Orders
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.OrbitReps

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native CFSG.Perm.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three
  CFSG.KC.Benes CFSG.KS.Fi24Net

noncomputable abbrev mTree : Tree := treeBFS degree 0 (mTabs ()) #[0, 1]

theorem hmLv : ∀ l ∈ (#[0, 1] : Array Nat), l < 2 := by
  intro l hl
  simp only [Array.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hl
  omega

theorem mem01 : (0 : Nat) ∈ (#[0, 1] : Array Nat) ∧ (1 : Nat) ∈ (#[0, 1] : Array Nat) := by simp

theorem hapM {j : Nat} (hj : j < 2) {x : Nat} (hx : x < 920808) :
    ap (mTabs ())[j]! x = eL NWP KAP KBP (Int.negSucc j) x := by
  rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
  · rw [mTabs_P.1 x hx, idx_of_lt _ hx, Perm.smul_def, gT_apply (lokP (by decide))]
  · rw [mTabs_P.2 x hx, idx_of_lt _ hx, Perm.smul_def, gT_apply (lokP (by decide))]

theorem hFM : ∀ l ∈ (#[0, 1] : Array Nat), ∀ x < degree, ap (mTabs ())[l]! x < degree := by
  intro l hl x hx
  have hl2 := hmLv l hl
  rw [hapM hl2 hx]
  exact eL_lt (lokP (by rw [Int.natAbs_negSucc]; omega)) hx

theorem mMin : ∀ P : Nat → Prop, P 0 → (∀ x, P x → ∀ l ∈ (#[0, 1] : Array Nat),
    P (ap (mTabs ())[l]! x)) → ∀ x, (fun x => decide (x < 920808)) x = true → P x := by
  have hg : ∀ z ∈ ([-1, -2] : List ℤ), LOK NWP KAP KBP z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> exact lokP (by decide)
  obtain ⟨-, -, hmin, hcnt⟩ := orb_spec (by decide) hg BridgeCk.trans
  have hall : ∀ N < 920808, memS (closeS NWP KAP KBP [-1, -2] 62 (single 0)) N = true := by
    have := List.length_filter_eq_length_iff.1 (by rw [hcnt, List.length_range])
    exact fun N hN => this N (List.mem_range.2 hN)
  have heL : ∀ (z : ℤ) (x : Nat), ¬ x < 920808 → eL NWP KAP KBP z x = x := by
    intro z x hx
    unfold eL
    rw [if_neg hx]
  intro P hP0 hP y hy
  have hy' : y < 920808 := of_decide_eq_true hy
  refine hmin P hP0 (fun N hN z hz => ?_) y hy' (hall y hy')
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  by_cases hN' : N < 920808
  · rcases hz with rfl | rfl
    · have := hP N hN 0 mem01.1
      rwa [hapM (by decide) hN'] at this
    · have := hP N hN 1 mem01.2
      rwa [hapM (by decide) hN'] at this
  · rw [heL z N hN']
    exact hN

theorem mTree_all {x : Nat} (hx : x < 920808) : ∃ k < mTree.pts.size, ap mTree.pts k = x :=
  (exists_treeBFS_pts_iff (O := fun x => decide (x < 920808)) hn32 (by decide) hFM (by decide)
    (fun x h => of_decide_eq_true h)
    (fun x h l hl => decide_eq_true (hFM l hl x (of_decide_eq_true h))) mMin x).2
    (decide_eq_true hx)

theorem mTree_size : mTree.pts.size = 920808 :=
  treeBFS_size (O := fun x => decide (x < 920808)) hn32 (by decide) hFM (by decide)
    (fun x h => of_decide_eq_true h)
    (fun x h l hl => decide_eq_true (hFM l hl x (of_decide_eq_true h))) mMin
    (by
      rw [List.filter_eq_self.2 (fun x hx => decide_eq_true (List.mem_range.1 hx)),
        List.length_range])

theorem mTree_ok : treeOK degree 0 mTree (mTabs ()) #[0, 1] = true :=
  treeOK_treeBFS hn32 (by decide) hFM (fun l hl => by have := hmLv l hl; omega)


theorem mTree_facts : CFSG.Perm.TreeFacts 920808 mTree #[0, 1] mQ 0 :=
  CFSG.Perm.treeOK_facts (fun l hl => rep_mQ (hmLv l hl)) mTree_ok

@[expose] def twStep (T : Tree) (_ : Nat) (s : List Int × Nat) : Id (ForInStep (List Int × Nat)) :=
  if 0 < s.2 then ForInStep.yield (s.1 ++ [Int.ofNat (ap T.lab s.2) + 1], ap T.par s.2)
  else ForInStep.done s

theorem letterPerm_lab {a : Nat} (ha : a < 2) : letterPerm mQ 2 (Int.ofNat a + 1) = mQ a := by
  unfold letterPerm
  simp only [Int.ofNat_eq_coe]
  rw [if_pos (by constructor <;> omega)]
  congr 1
  omega

theorem loop_word : ∀ (l : List Nat) (w : List Int) (k : Nat), k < mTree.pts.size →
    k ≤ l.length → wordG (letterPerm mQ 2) (forIn l (w, k) (twStep mTree)).1 =
      wordG (letterPerm mQ 2) w * CFSG.Perm.treeG mTree mQ k
  | [], w, k, _, hl => by
    have : k = 0 := by simpa using hl
    subst this
    rw [CFSG.Perm.treeG_zero, mul_one, List.forIn_nil]
    try rfl
  | a :: l, w, k, hk, hl => by
    rw [List.forIn_cons]
    by_cases h0 : 0 < k
    · obtain ⟨hp, hlab⟩ := mTree_facts.par k hk h0
      have hl2 : ap mTree.lab k < 2 := hmLv _ hlab
      have hl' : k ≤ l.length + 1 := by simpa using hl
      have ih := loop_word l (w ++ [Int.ofNat (ap mTree.lab k) + 1]) (ap mTree.par k) (by omega)
        (by omega)
      have e : twStep mTree a (w, k) =
          ForInStep.yield (w ++ [Int.ofNat (ap mTree.lab k) + 1], ap mTree.par k) := by
        unfold twStep
        rw [if_pos h0]
      rw [e]
      refine Eq.trans ?_ (ih.trans ?_)
      · rfl
      · conv_rhs => rw [CFSG.Perm.treeG.eq_def]
        rw [dif_pos ⟨h0, hp⟩]
        simp only [wordG, List.map_append, List.prod_append, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, mul_one, mul_assoc]
        rw [letterPerm_lab hl2]
    · have : k = 0 := by omega
      subst this
      have e : twStep mTree a (w, 0) = ForInStep.done (w, 0) := by
        unfold twStep
        rw [if_neg h0]
      rw [e, CFSG.Perm.treeG_zero, mul_one]
      try rfl

theorem wordG_treeWord {p : Nat} (hp : ap mTree.pos p < mTree.pts.size) :
    wordG (letterPerm mQ 2) (treeWord mTree p) = CFSG.Perm.treeG mTree mQ (ap mTree.pos p) := by
  unfold treeWord
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hlen : ap mTree.pos p ≤ (List.range' 0 ((degree - 0 + 1 - 1) / 1)).length := by
    rw [mTree_size] at hp
    simp only [List.length_range', degree]
    omega
  have h := loop_word (List.range' 0 ((degree - 0 + 1 - 1) / 1)) [] (ap mTree.pos p) hp hlen
  have e : wordG (letterPerm mQ 2) ([] : List Int) = 1 := by simp [wordG]
  rw [e, one_mul] at h
  exact h

theorem geomWords_get {i : Nat} (hi : i < 7) :
    (geomWords (mTabs ()))[i]! = treeWord mTree (gRoot i) := by
  unfold geomWords
  dsimp only
  rw [getElem!_pos _ i (by simp [geomReps]; omega), Array.getElem_map, ← geomReps_get hi,
    getElem!_pos geomReps i (by simp [geomReps]; omega)]

theorem geomWords_size : (geomWords (mTabs ())).size = 7 := by simp [geomWords, geomReps]

theorem repTabs_rep {i : Nat} (hi : i < 7) :
    Rep 920808 (repTabs (mTabs ()) (geomWords (mTabs ())))[i]!
      (wordG (letterPerm mQ 2) (treeWord mTree (gRoot i))) := by
  have hw : i < (geomWords (mTabs ())).size := by rw [geomWords_size]; exact hi
  have e : (repTabs (mTabs ()) (geomWords (mTabs ())))[i]! =
      wordT 920808 (letterTab 920808 (mTabs ()) ((mTabs ()).map (invT 920808)))
        (geomWords (mTabs ()))[i]! := by
    simp only [repTabs]
    rw [getElem!_pos _ _ (by simpa using hw), Array.getElem_map,
      getElem!_pos (geomWords (mTabs ())) _ hw]
  rw [e, geomWords_get hi]
  exact rep_wordT_m _

theorem word_smul_x0 {r : Nat} (hr : r < 920808) :
    ((wordG (letterPerm mQ 2) (treeWord mTree r)) • x0).val = r := by
  obtain ⟨j, hj, hjr⟩ := mTree_all hr
  have hpos : ap mTree.pos r = j := hjr ▸ mTree_facts.pos_pts j hj
  rw [wordG_treeWord (hpos ▸ hj), hpos, ← hjr]
  have h := mTree_facts.elt j hj
  rw [idx_of_lt _ (by decide : 0 < 920808)] at h
  exact h

theorem mQ_act {j : Nat} (hj : j < 2) (x : Ω) :
    (mQ j • x).val = eL NWP KAP KBP (Int.negSucc j) x.val := by
  rw [smul_val_of_rep (rep_mQ hj) x, hapM hj x.isLt]

theorem exists_wordQ : ∀ w : List ℤ, (∀ z ∈ w, z = -1 ∨ z = -2) →
    ∃ h : Q3, ∀ x : Ω, (h • x).val = eW NWP KAP KBP w x.val
  | [], _ => ⟨1, fun x => by rw [one_smul]; rfl⟩
  | z :: w, hw => by
    obtain ⟨h, hh⟩ := exists_wordQ w fun z' hz' => hw z' (List.mem_cons_of_mem z hz')
    rcases hw z List.mem_cons_self with rfl | rfl
    · refine ⟨mQ 0 * h, fun x => ?_⟩
      have := mQ_act (j := 0) (by decide) (h • x)
      rw [hh] at this
      rw [mul_smul]
      exact this
    · refine ⟨mQ 1 * h, fun x => ?_⟩
      have := mQ_act (j := 1) (by decide) (h • x)
      rw [hh] at this
      rw [mul_smul]
      exact this

theorem gMW_letters {i : Nat} (hi : i < 7) : ∀ z ∈ gMW i, z = -1 ∨ z = -2 := by
  interval_cases i <;> decide

theorem gMW_lok {i : Nat} (hi : i < 7) : ∀ z ∈ gMW i, LOK NWP KAP KBP z := by
  intro z hz
  rcases gMW_letters hi z hz with rfl | rfl <;> exact lokP (by decide)

noncomputable abbrev gLab : Table := geomLab (geomTrees (genTabs ()))

theorem lab_smul_genQ {l : Nat} (hl : l ∈ zpLetters) (v : Ω) :
    ap gLab (genQ l • v).val = ap gLab v.val := by
  rw [smul_val_of_rep (rep_genQ (hzl l hl)) v]
  obtain ⟨i, hi, h⟩ := exists_gS v.val v.isLt
  have hgv : ap (genTabs ())[l]! v.val < 920808 := by
    rw [hapZ l hl v.val v.isLt]
    exact eL_lt (hgZ _ (by rw [hzL]; exact List.mem_map.2 ⟨l, by simpa using hl, rfl⟩)) v.isLt
  rw [ap_geomLab hi hgv (closed_mem hi v.isLt h hl), ap_geomLab hi v.isLt h]

theorem lab_smul_Zp {k : Q3} (hk : k ∈ Zp) (v : Ω) : ap gLab (k • v).val = ap gLab v.val := by
  rw [← lettersGroup_zpLetters] at hk
  exact CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.smul_apply_eq_of_mem_closure
    (S := {g | ∃ l ∈ zpLetters, genQ l = g}) (F := fun v : Ω => ap gLab v.val) (fun s hs v => by
      obtain ⟨l, hl, rfl⟩ := hs
      exact lab_smul_genQ hl v) k hk v

theorem memS_of_lab {i : Nat} {x : Nat} (hx : x < 920808) (h : ap gLab x = i) :
    memS (gS i) x = true := by
  obtain ⟨j, hj, hm⟩ := exists_gS x hx
  rw [ap_geomLab hj hx hm] at h
  subst h
  exact hm

theorem lab_lt (x : Nat) (hx : x < 920808) : ap gLab x < 7 ∧ memS (gS (ap gLab x)) x = true := by
  obtain ⟨j, hj, hm⟩ := exists_gS x hx
  rw [ap_geomLab hj hx hm]
  exact ⟨hj, hm⟩

theorem img_rep {i : Nat} (hi : i < 7) (g : Q3) (hg : (g • x0).val = gRoot i) :
    (∀ c : Ω, memS (gS 1) c.val = true →
        memS (imgW NWP KAP KBP (gMW i) (gS 1)) (g • c).val = true) ∧
      ∀ c : Ω, memS (imgW NWP KAP KBP (gMW i) (gS 1)) c.val = true →
        ∃ c' : Ω, memS (gS 1) c'.val = true ∧ g • c' = c := by
  obtain ⟨h, hh⟩ := exists_wordQ (gMW i) (gMW_letters hi)
  have hw := gMW_lok hi
  have h0 : h • x0 = g • x0 := Fin.ext (by
    rw [hh, x0_val, hg]
    exact ptOK_spec hw (by decide) (gRoot_lt hi) (gFacts.root i hi))
  have hk : g⁻¹ * h ∈ Zp := by
    rw [Zp_eq_stabilizer, MulAction.mem_stabilizer_iff, mul_smul, h0, inv_smul_smul]
  have hS1 : ∀ k : Q3, k ∈ Zp → ∀ c : Ω, memS (gS 1) c.val = true →
      memS (gS 1) (k • c).val = true := fun k hk c hc =>
    memS_of_lab (k • c).isLt (by rw [lab_smul_Zp hk, ap_geomLab (i := 1) (by decide) c.isLt hc])
  have himg : ∀ c : Ω, memS (imgW NWP KAP KBP (gMW i) (gS 1)) (h • c).val = memS (gS 1) c.val :=
    fun c => by
      rw [hh]
      exact memS_imgW _ hw _ c.isLt
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have e : g • c = h • ((g⁻¹ * h)⁻¹ • c) := by
      rw [mul_inv_rev, inv_inv, mul_smul, smul_inv_smul]
    rw [e, himg]
    exact hS1 _ (inv_mem hk) c hc
  · refine ⟨(g⁻¹ * h) • (h⁻¹ • c), hS1 _ hk _ ?_, ?_⟩
    · rw [← himg (h⁻¹ • c), smul_inv_smul]
      exact hc
    · rw [mul_smul, smul_inv_smul, smul_inv_smul]

theorem gWit_lt {i : Nat} (hi : i < 7) : gWit i < 920808 := by interval_cases i <;> decide

theorem gWl_lt {i : Nat} (hi : i < 7) : gWl i < 7 := by interval_cases i <;> decide

theorem distOK_true :
    distOK gLab (repTabs (mTabs ()) (geomWords (mTabs ()))) (geomTrees (genTabs ()))[1]!.pts =
      true := by
  have hok := (gTree (i := 1) (by decide)).2.1
  have hS1 := (gTree (i := 1) (by decide)).2.2
  rw [← geomTrees_get (i := 1) (by decide)] at hS1 hok
  set G := (geomTrees (genTabs ()))[1]!
  have hpt : ∀ j (hj : j < G.pts.size), (G.pts[j]).toNat < 920808 ∧
      memS (gS 1) (G.pts[j]).toNat = true := by
    intro j hj
    have hc : ap G.pts j = (G.pts[j]).toNat := by simp only [ap, getElem!_pos G.pts j hj]
    have hclt : (G.pts[j]).toNat < 920808 := hc ▸ pts_lt_of_treeOK hok hj
    exact ⟨hclt, (hS1 _ hclt).1 ⟨j, hj, hc⟩⟩
  unfold distOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨by simp [repTabs, geomWords_size], rfl⟩,
    allIn_eq_true.2 fun i _ hi => by interval_cases i <;> rfl⟩,
    allIn_eq_true.2 fun i _ hi => ?_⟩
  set T := (repTabs (mTabs ()) (geomWords (mTabs ())))[i]!
  set g := wordG (letterPerm mQ 2) (treeWord mTree (gRoot i))
  have hT : Rep 920808 T g := repTabs_rep hi
  have hg : (g • x0).val = gRoot i := word_smul_x0 (gRoot_lt hi)
  obtain ⟨hA, hB⟩ := img_rep hi g hg
  have hTc : ∀ x (hx : x < 920808), ap T x = (g • (⟨x, hx⟩ : Ω)).val :=
    fun x hx => (smul_val_of_rep hT ⟨x, hx⟩).symm
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq, Array.any_eq_true,
    Array.all_eq_true, geomLevels_get hi, geomReps_get hi]
  refine ⟨⟨by rw [hTc 0 (by decide)]; exact hg, ?_⟩, fun j hj => ?_⟩
  · rcases gFacts.down i hi with h0 | ⟨hw1, hw2, hw3⟩
    · exact Or.inl h0
    · right
      rw [gsel (i := 1) (by decide)] at hw1
      obtain ⟨c', hc', hgc⟩ := hB ⟨gWit i, gWit_lt hi⟩ hw1
      obtain ⟨j, hj, hjc⟩ := (hS1 c'.val c'.isLt).2 hc'
      have hc : ap G.pts j = (G.pts[j]).toNat := by simp only [ap, getElem!_pos G.pts j hj]
      refine ⟨j, hj, ?_⟩
      have e : ap T (G.pts[j]).toNat = gWit i := by
        rw [← hc, hjc, hTc _ c'.isLt, Fin.eta, hgc]
      rw [e]
      rw [gsel (gWl_lt hi)] at hw2
      rw [ap_geomLab (gWl_lt hi) (gWit_lt hi) hw2, geomLevels_get (gWl_lt hi), hw3]
  · obtain ⟨hclt, hcS⟩ := hpt j hj
    have hy : memS (imgW NWP KAP KBP (gMW i) (gS 1)) (ap T (G.pts[j]).toNat) = true := by
      rw [hTc _ hclt]
      exact hA ⟨_, hclt⟩ hcS
    have hylt : ap T (G.pts[j]).toNat < 920808 := by
      rw [hTc _ hclt]
      exact (g • (⟨_, hclt⟩ : Ω)).isLt
    obtain ⟨hl7, hm⟩ := lab_lt _ hylt
    rw [geomLevels_get hl7]
    by_contra hlt
    have hd := gFacts.up i hi _ hl7 (by omega)
    rw [gsel hl7, gsel (i := 1) (by decide)] at hd
    exact disj_memS hd _ ⟨hy, hm⟩

theorem geomOK_true : geomOK () = true := by
  unfold geomOK geomOKAt
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨geomWords_size, zpTreesOK_true⟩, labOK_true⟩, distOK_true⟩, s1OK_true⟩

end CertificateChecks.KernelRouteP

end

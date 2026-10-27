module

public import Certificates.Kernel.RouteP.Obj.Glue

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.Sporadic.LevelChain.Native CFSG.YGroups CFSG.Sporadic.Recognition.Fi22Multiplier

theorem y332Reg_eq : y332Reg = yReg := by
  funext j
  unfold y332Reg yReg
  rfl

theorem yReg_lt {j : Nat} (hj : j < 71) : yReg j < 112 := by
  unfold yReg
  split_ifs <;> omega

theorem lokY_reg {r : Nat} (hr : r < 112) : LOK NWY KAY KBY (Int.ofNat (r + 1)) := lokY (by simp; omega)

theorem negSucc_eq' (r : Nat) : -((r + 1 : Nat) : ℤ) = Int.negSucc r := by
  rw [Int.negSucc_eq]
  omega

theorem letterPerm_pos {G : Type*} [Group G] (π : ℕ → G) {m k : Nat} (hk : k < m) :
    letterPerm π m ((k : ℤ) + 1) = π k := by
  unfold letterPerm
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  omega

theorem letterPerm_neg {G : Type*} [Group G] (π : ℕ → G) {m k : Nat} (hk : k < m) :
    letterPerm π m (-((k : ℤ) + 1)) = (π k)⁻¹ := by
  unfold letterPerm
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
  congr 2
  omega

theorem wordG_y332Word {π : ℕ → Perm Pt} (hπ : ∀ j < 71, π j = gY (yReg j)) {l : List ℤ}
    (h : ∀ p ∈ pairsOf l, y332Idx p.1 < 71 ∧ yReg (y332Idx p.1) = p.1 - 1) :
    wordG (letterPerm π 71) (y332Word l) = lineProd gY l := by
  unfold y332Word lineProd
  rw [wordG_flatMap]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  by_cases hs : p.2 < 0
  · rw [if_pos hs, wordG_replicate, letterPerm_neg π h1, hπ _ h1, h2]
    have hp2 : p.2 = -(p.2.natAbs : ℤ) := by omega
    conv_rhs => rw [hp2]
    rw [zpow_neg, zpow_natCast, inv_pow]
  · rw [if_neg hs, wordG_replicate, letterPerm_pos π h1, hπ _ h1, h2]
    have hp2 : p.2 = (p.2.natAbs : ℤ) := by omega
    conv_rhs => rw [hp2]
    rw [zpow_natCast]

@[expose] def zOf (l : Nat) : ℤ :=
  if l % 2 = 0 then -((yReg (l / 2) + 1 : Nat) : ℤ) else ((yReg (l / 2) + 1 : Nat) : ℤ)

theorem lv_facts : ∀ i < 8, (∀ l ∈ (levelLv y332Starts i).toList, l < 142) ∧
    yLetters i = (levelLv y332Starts i).toList.map zOf ∧ y332Base[i]! = yBase[i]! ∧
    y332Sizes[i]! = ySizes[i]! ∧ y332Base[i]! < 920808 := by
  decide +kernel

theorem base_facts : ∀ i < 8, ∀ j < 71, (1 ≤ i ∧ y332Starts[i]! ≤ j ∧ j < y332Starts[i + 1]!) →
    9 ≤ j ∧ yBase[yLevel j - 1]! = y332Base[i - 1]! := by
  decide +kernel

theorem nest_range : ∀ i < 8, ∀ j < 71, (1 ≤ i ∧ y332Starts[i]! ≤ j ∧ j < y332Starts[i + 1]!) →
    (y332Word y332LinesK.toArray[j + 39]!).all (fun z => decide (y332Starts[i - 1]! + 1 ≤ z.natAbs) &&
      decide (z.natAbs ≤ y332Starts[i]!)) = true := by
  decide +kernel

theorem nest_idx : ∀ j < 71, 9 ≤ j →
    ∀ p ∈ pairsOf y332LinesK.toArray[j + 39]!, y332Idx p.1 < 71 ∧ yReg (y332Idx p.1) = p.1 - 1 := by
  decide +kernel

theorem yWs_facts : yWs.length = 47 ∧ ∀ w ∈ yWs, ∀ c ∈ w, c < 9 := by
  decide +kernel

theorem y332Gens_get {R : Array Table} {j : Nat} (hj : j < 71) : (y332Gens R)[j]! = R[yReg j]! := by
  unfold y332Gens
  rw [getElem!_map_range _ hj, y332Reg_eq]

theorem y332Letters_get {gs : Array Table} {l : Nat} (hl : l < 142) :
    (y332Letters gs)[l]! = if l % 2 = 0 then gs[l / 2]! else invT degree gs[l / 2]! := by
  unfold y332Letters
  rw [getElem!_pos _ l (by simp; omega), Array.getElem_ofFn]

theorem y332NineOK_of {R : Array Table} (hR : ∀ r < 112, Rep 920808 R[r]! (gY r)) :
    y332NineOK ((y332Gens R).extract 0 9)
      ((yRels 3 3 2 ++ [f332Word]).map fun w => w.map fun (c : Nat) => (c : Int) + 1) = true := by
  set g9 := (y332Gens R).extract 0 9
  have hsz : (y332Gens R).size = 71 := by simp [y332Gens]
  have h9 : g9.size = 9 := by simp [g9, hsz]
  have hget : ∀ j < 9, g9[j]! = R[yReg j]! := by
    intro j hj
    rw [← y332Gens_get (by omega)]
    simp only [g9]
    rw [getElem!_pos _ j (by rw [h9]; exact hj), getElem!_pos _ j (by rw [hsz]; omega),
      Array.getElem_extract]
    simp
  have hrep : ∀ l < g9.size, Rep 920808 g9[l]! (gY (yReg l)) := by
    intro l hl
    rw [h9] at hl
    rw [hget l hl]
    exact hR _ (yReg_lt (by omega))
  unfold y332NineOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨h9, ?_⟩, ?_⟩
  · rw [allIn_eq_true]
    intro j _ hj
    simp only [Bool.and_eq_true, beq_iff_eq]
    have hr := yReg_lt (j := j) (by omega)
    have hf : ∀ b < 2, ptOK NWY KAY KBY [((yReg j + 1 : Nat) : Int)] (if b = 0 then 0 else 1479)
        (if b = 0 then 0 else 1479) = true := by
      intro b hb
      have h := yfix_all (2 * j + b) (by have h' : 2 * j + b < 18 := (by omega); exact h')
      unfold yfix at h
      have e1 : Nat.div (2 * j + b) 2 = j := by change (2 * j + b) / 2 = j; omega
      have e2 : Nat.mod (2 * j + b) 2 = b := by change (2 * j + b) % 2 = b; omega
      rw [e1, e2] at h
      rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
      · exact h
      · exact h
    rw [hget j hj]
    exact ⟨ap_of_ptOK (hR _ hr) (lokY_reg hr) (by decide) (by decide) (hf 0 (by decide)),
      ap_of_ptOK (hR _ hr) (lokY_reg hr) (by decide) (by decide) (hf 1 (by decide))⟩
  · unfold relatorsOK
    rw [List.all_eq_true]
    intro w hw
    have h1 := rep_wordT_letters (G := Perm Pt) (n := 920808) hn32 (gs := g9) (π := fun j => gY (yReg j))
      hrep (fun l hl => invOK_invT_of_rep hn32 (hrep l hl)) w
    rw [h9] at h1
    refine eqTab_of_rep h1 ?_
    have e : wordG (letterPerm (fun j => gY (yReg j)) 9) w = 1 := by
      obtain ⟨w0, hw0, rfl⟩ := List.mem_map.1 hw
      have hw0' : w0 ∈ yWs := hw0
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw0'
      have hi47 : i < 47 := by rw [← yWs_facts.1]; exact hi
      have hlet := yWs_facts.2 _ (List.getElem_mem hi)
      set cf : ℤ → ℤ := fun l => -((yReg (l.toNat - 1) + 1 : Nat) : ℤ)
      have hyw : (yWs[i].map fun (c : Nat) => (c : Int) + 1).map cf = yw i := by
        unfold yw
        rw [getElem!_pos yWs i hi, List.map_map]
        apply List.map_congr_left
        intro c _
        simp only [Function.comp, cf]
        rw [show ((c : ℤ) + 1).toNat - 1 = c by omega]
      have hyk : ∀ k < 20, yck (20 * i + k) = true := fun k hk =>
        yck_all (20 * i + k) (by have h' : 20 * i + k < 940 := (by omega); exact h')
      refine wordG_eq_one (NW := NWY) (KA := KAY) (KB := KBY) _ cf (fun l hl y => ?_) ?_ ?_ ?_
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
        have hc9 := hlet c hc
        rw [letterPerm_pos _ hc9]
        simp only [cf]
        rw [show ((c : ℤ) + 1).toNat - 1 = c by omega, negSucc_eq']
        exact gT_apply (lokY_reg (yReg_lt (by omega))) y
      · have hW : WOK NWY KAY KBY (yw i) := by
          intro z hz
          unfold yw at hz
          rw [getElem!_pos yWs i hi] at hz
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hz
          have hr := yReg_lt (j := c) (by have := hlet c hc; omega)
          exact lokY (by simp; omega)
        rw [← hyw] at hW
        exact hW
      · intro k hk
        have h := hyk k (by omega)
        unfold yck at h
        have e1 : Nat.mod (20 * i + k) 20 = k := by change (20 * i + k) % 20 = k; omega
        have e2 : Nat.div (20 * i + k) 20 = i := by change (20 * i + k) / 20 = i; omega
        rw [e1, e2, Nat.blt_eq.mpr hk, ← hyw] at h
        exact h
      · have h := hyk 19 (by omega)
        unfold yck at h
        have e1 : Nat.mod (20 * i + 19) 20 = 19 := by change (20 * i + 19) % 20 = 19; omega
        have e2 : Nat.div (20 * i + 19) 20 = i := by change (20 * i + 19) / 20 = i; omega
        rw [e1, e2, show Nat.blt 19 19 = false from rfl, ← hyw] at h
        exact h
    rw [e]
    exact Rep.idT hn32

theorem y332OKAt_of (hm : Rep 920808 (mTabs ())[0]! (gY 0) ∧ Rep 920808 (mTabs ())[1]! (gY 1)) :
    y332OKAt (y332Run ())
      ((yRels 3 3 2 ++ [f332Word]).map fun w => w.map fun (c : Nat) => (c : Int) + 1) = true := by
  have hR : ∀ r < 112, Rep 920808 (y332Run ()).1[r]! (gY r) := y332Run_rep hm
  have hrun := mRun_flag (extra := 111) (prog := y332Prog ()) hm y332Prog_ok
  set R := (y332Run ()).1 with hRdef
  set gens := y332Gens R
  set letters := y332Letters gens
  have hgsz : gens.size = 71 := by simp [gens, y332Gens]
  have hG : ∀ j < 71, Rep 920808 gens[j]! (gY (yReg j)) := by
    intro j hj
    rw [y332Gens_get hj]
    exact hR _ (yReg_lt hj)
  have hL : ∀ l < 142, Rep 920808 letters[l]!
      (if l % 2 = 0 then gY (yReg (l / 2)) else (gY (yReg (l / 2)))⁻¹) := by
    intro l hl
    rw [y332Letters_get hl]
    split_ifs
    · exact hG _ (by omega)
    · exact rep_invT hn32 (hG _ (by omega))
  have hapL : ∀ l < 142, ∀ x (hx : x < 920808), ap letters[l]! x = eL NWY KAY KBY (zOf l) x := by
    intro l hl x hx
    have hr := yReg_lt (j := l / 2) (by omega)
    rw [hL l hl x hx, idx_of_lt _ hx, Perm.smul_def]
    unfold zOf
    split_ifs
    · rw [negSucc_eq']
      exact gT_apply (lokY_reg hr) _
    · exact gT_inv_apply (lokY_reg hr) _
  have hF : ∀ l < 142, ∀ x < degree, ap letters[l]! x < degree := by
    intro l hl x hx
    rw [hL l hl x hx]
    exact idx_lt _ hx
  have hlv : ∀ i < 8, ∀ l ∈ levelLv y332Starts i, l < 142 :=
    fun i hi l hl => (lv_facts i hi).1 l (by simpa using hl)
  have hz : ∀ l < 142, LOK NWY KAY KBY (zOf l) := by
    intro l hl
    have hr := yReg_lt (j := l / 2) (by omega)
    unfold zOf
    split_ifs <;> exact lokY (by simp; omega)
  have htrees : y332TreesOK letters (levelTrees degree letters y332Starts y332Base) = true := by
    have hbsz : y332Base.size = 8 := rfl
    unfold y332TreesOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · simp [letters, y332Letters]
      rfl
    · rw [allIn_eq_true]
      intro j _ hj
      rw [y332Letters_get (by omega), y332Letters_get (by omega), if_pos (by omega), if_neg (by omega),
        show (2 * j + 1) / 2 = j by omega, show 2 * j / 2 = j by omega]
      exact invOK_invT_of_rep hn32 (hG j hj)
    · simp [levelTrees, hbsz]
    · rw [allIn_eq_true]
      intro i _ hi
      exact treeOK_levelTrees hn32 (by rw [hbsz]; exact hi) (lv_facts i hi).2.2.2.2
        (fun l hl x hx => hF l (hlv i hi l hl) x hx) (fun l hl => by have := hlv i hi l hl; omega)
    · rw [allIn_eq_true]
      intro i hi1 hi
      rw [allIn_eq_true]
      intro j hj1 hj2
      have hjs : j < 71 := by
        have : y332Starts[i + 1]! ≤ 71 := by interval_cases i <;> decide
        omega
      obtain ⟨h9, hb⟩ := base_facts i hi j hjs ⟨hi1, hj1, hj2⟩
      rw [beq_iff_eq, y332Letters_get (by omega), if_pos (by omega), show 2 * j / 2 = j by omega,
        y332Gens_get hjs]
      have h := ybase_all (j - 9) (by have h' : j - 9 < 62 := (by omega); exact h')
      unfold ybase9 at h
      rw [show j - 9 + 9 = j by omega] at h
      unfold ybase at h
      rw [hb] at h
      have hx := (lv_facts (i - 1) (by omega)).2.2.2.2
      exact ap_of_ptOK (hR _ (yReg_lt hjs)) (lokY_reg (yReg_lt hjs)) hx hx h
    · rw [allIn_eq_true]
      intro i _ hi
      obtain ⟨hl142, hyl, hbase, hsize, hblt⟩ := lv_facts i hi
      rw [beq_iff_eq, levelTrees_get (by rw [hbsz]; exact hi), hsize, hbase]
      have hg : ∀ z ∈ yLetters i, LOK NWY KAY KBY z := by
        intro z hzm
        rw [hyl] at hzm
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hzm
        exact hz l (hl142 l hl)
      have hb' : yBase[i]! < 920808 := by rw [← hbase]; exact hblt
      obtain ⟨hroot, hcl, hmin, hcnt⟩ := orb_spec hb' hg (ylev_all i hi)
      set S := closeS NWY KAY KBY (yLetters i) (yRounds[i]!) (single (yBase[i]!))
      refine treeBFS_size (O := fun x => decide (x < 920808) && memS S x) hn32 hb'
        (fun l hl x hx => hF l (hlv i hi l hl) x hx)
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hb', hroot⟩)
        (fun x hx => by simp only [Bool.and_eq_true, decide_eq_true_eq] at hx; exact hx.1)
        (fun x hx l hl => ?_) (fun P hP0 hP x hx => ?_) ?_
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
        have hl' := hlv i hi l hl
        have hzm : zOf l ∈ yLetters i := by
          rw [hyl]
          exact List.mem_map.2 ⟨l, by simpa using hl, rfl⟩
        rw [hapL l hl' x hx.1]
        exact ⟨eL_lt (hz l hl') hx.1, hcl x hx.1 hx.2 _ hzm⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
        refine hmin P hP0 (fun N hN z hzm => ?_) x hx.1 hx.2
        rw [hyl] at hzm
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hzm
        have hl' : l ∈ levelLv y332Starts i := by simpa using hl
        by_cases hN' : N < 920808
        · rw [← hapL l (hlv i hi l hl') N hN']
          exact hP N hN l hl'
        · unfold eL
          rw [if_neg hN']
          exact hN
      · rw [← hcnt]
        exact congrArg List.length (List.filter_congr fun x hx => by
          have hx' : x < 920808 := List.mem_range.1 hx
          simp [hx'])
  have hnest : y332NestOK gens (y332Lines ()) = true := by
    unfold y332NestOK
    simp only
    rw [allIn_eq_true]
    intro i hi1 hi
    rw [allIn_eq_true]
    intro j hj1 hj2
    have hjs : j < 71 := by
      have : y332Starts[i + 1]! ≤ 71 := by interval_cases i <;> decide
      omega
    have h9 := (base_facts i hi j hjs ⟨hi1, hj1, hj2⟩).1
    have hℓ : j + 39 < 110 := by omega
    have hall := nest_range i hi j hjs ⟨hi1, hj1, hj2⟩
    have hidx := nest_idx j hjs h9
    rw [y332Lines_eq, Bool.and_eq_true]
    refine ⟨hall, ?_⟩
    have h1 := rep_wordT_letters (G := Perm Pt) (n := 920808) hn32 (gs := gens) (π := fun j => gY (yReg j))
      (fun l hl => hG l (by rw [hgsz] at hl; exact hl))
      (fun l hl => invOK_invT_of_rep hn32 (hG l (by rw [hgsz] at hl; exact hl)))
      (y332Word y332LinesK.toArray[j + 39]!)
    rw [hgsz, wordG_y332Word (fun j _ => rfl) hidx] at h1
    refine eqTab_of_rep h1 ?_
    have hs := y332Lines_size
    have hsK : y332LinesK.toArray.size = 110 := by rw [← y332Lines_eq]; exact hs
    have hls := y332Lines_linesOK
    rw [y332Lines_eq] at hls
    have hck : ∀ k < 20, lineOK NWY KAY KBY y332LinesK.toArray 0 (fun ℓ => 2 + ℓ) (20 * (j + 39) + k) =
        true := fun k hk =>
      ylck_all _ (by have h' : 20 * (j + 39) + k < 2200 := (by omega); exact h')
    have hspec := lineOK_spec hck
    have hline := line_spec (NW := NWY) (KA := KAY) (KB := KBY) (o := 0) (j := 2 + (j + 39))
      (lokY_reg (by omega))
      (fun z hzm => by
        unfold lineW at hzm
        obtain ⟨p, hp, hzm⟩ := List.mem_flatMap.1 hzm
        have h1 := hls (j + 39) (by rw [hsK]; exact hℓ) p (List.mem_reverse.1 hp)
        have := (List.mem_replicate.1 hzm).2
        refine lokY ?_
        split_ifs at this <;> subst this <;> simp <;> omega)
      (fun p hp => (hls (j + 39) (by rw [hsK]; exact hℓ) p hp).1) hspec.1 hspec.2
    have e : lineProd (fun r => gT NWY KAY KBY (r + 0)) y332LinesK.toArray[j + 39]! =
        lineProd gY y332LinesK.toArray[j + 39]! := lineProd_congr fun p _ => rfl
    rw [e, show 2 + (j + 39) = yReg j by unfold yReg; rw [if_neg (by omega)]; omega] at hline
    rw [← hline, y332Gens_get hjs]
    exact hR _ (yReg_lt hjs)
  unfold y332OKAt
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hrun.1, hrun.2⟩, y332Prog_ok⟩, y332DataOK_true⟩, hgsz⟩, y332NineOK_of hR⟩, htrees⟩, hnest⟩

end CertificateChecks.KernelRouteP

end

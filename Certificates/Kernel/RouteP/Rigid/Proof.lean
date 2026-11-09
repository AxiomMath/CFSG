module

public import Certificates.Kernel.RouteP.Rigid.Checks
public import CFSG.Certificates.Kernel.RouteP.RigidTwin
public import CFSG.Certificates.Kernel.RouteP.TabComplete
public import CFSG.Certificates.Kernel.Spor.PK.NatChain
public import Certificates.Kernel.RouteP.Text.PlaneFacts

public section

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KD.RouteP CFSG.KS.RouteP CFSG.KS.PK CFSG.Sporadic.Th.Native
  CFSG.Perm.Native CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Rigid.Native

theorem bit_test (m q : Nat) : Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 q)) = m.testBit q := by
  rw [Nat.land_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow]
  cases m.testBit q
  · simp only [Bool.toNat_false, Nat.zero_mul]
    rfl
  · simp only [Bool.toNat_true, Nat.one_mul]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos q)

theorem testBit_lor_bit (m x q : Nat) :
    (Nat.lor m (Nat.shiftLeft 1 x)).testBit q = (m.testBit q || decide (q = x)) := by
  rw [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul,
    Nat.testBit_two_pow]
  cases m.testBit q <;> simp [eq_comm]

theorem rgSnoc_eq (x : Nat) : ∀ l : List Nat, rgSnoc l x = l ++ [x]
  | [] => rfl
  | a :: l => congrArg (a :: ·) (rgSnoc_eq x l)

theorem rgLen_eq : ∀ l : List Nat, rgLen l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (rgLen_eq l)

theorem rgFold_eq {β : Type} (f : β → Nat → β) : ∀ (l : List Nat) (b : β), rgFold f l b = l.foldl f b
  | [], _ => rfl
  | x :: l, b => rgFold_eq f l (f b x)

theorem getK_eq : ∀ (l : List Nat) (k : Nat), getK l k = l.getD k 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: xs, k + 1 => by
    change getK xs k = _
    rw [getK_eq xs k]
    rfl

def MaskOK (st : BS × Nat) : Prop := ∀ q, st.2.testBit q = decide (q ∈ st.1.pts)

theorem letterM_ok (F : Nat → Nat → Nat) (h p l : Nat) {st : BS × Nat} (hs : MaskOK st) :
    MaskOK (letterM F h p st l) ∧ (letterM F h p st l).1 = BS.letter F h p st.1 l := by
  unfold letterM BS.letter
  simp only [rgSnoc_eq]
  rw [bit_test, hs]
  by_cases hm : F l p ∈ st.1.pts
  · rw [decide_eq_true hm, if_pos hm]
    exact ⟨hs, rfl⟩
  · rw [decide_eq_false hm, if_neg hm]
    refine ⟨fun q => ?_, rfl⟩
    change (Nat.lor st.2 (Nat.shiftLeft 1 (F l p))).testBit q = decide (q ∈ st.1.pts ++ [F l p])
    rw [testBit_lor_bit, hs]
    by_cases hq : q = F l p
    · subst hq
      simp
    · simp [hq, List.mem_append]

theorem foldl_letterM_ok (F : Nat → Nat → Nat) (h p : Nat) :
    ∀ (lv : List Nat) (st : BS × Nat), MaskOK st →
      MaskOK (lv.foldl (letterM F h p) st) ∧
        (lv.foldl (letterM F h p) st).1 = lv.foldl (BS.letter F h p) st.1
  | [], _, hs => ⟨hs, rfl⟩
  | l :: lv, st, hs => by
    obtain ⟨h1, h2⟩ := letterM_ok F h p l hs
    obtain ⟨h3, h4⟩ := foldl_letterM_ok F h p lv _ h1
    exact ⟨h3, by rw [List.foldl_cons, List.foldl_cons, h4, h2]⟩

theorem stepM_ok (F : Nat → Nat → Nat) (lv : List Nat) (h : Nat) {st : BS × Nat}
    (hs : MaskOK st) : MaskOK (stepM F lv st h) ∧ (stepM F lv st h).1 = BS.step F lv st.1 h := by
  unfold stepM BS.step
  rw [rgFold_eq, getK_eq, rgLen_eq]
  by_cases hh : h < st.1.pts.length
  · rw [(Nat.blt_eq.mpr hh : Nat.blt h st.1.pts.length = true), if_pos hh]
    exact foldl_letterM_ok F h _ lv st hs
  · rw [(Bool.eq_false_iff.mpr fun e => hh (Nat.blt_eq.mp e) :
      Nat.blt h st.1.pts.length = false), if_neg hh]
    exact ⟨hs, rfl⟩

theorem foldl_stepM_ok (F : Nat → Nat → Nat) (lv : List Nat) :
    ∀ (hs : List Nat) (st : BS × Nat), MaskOK st →
      MaskOK (hs.foldl (stepM F lv) st) ∧
        (hs.foldl (stepM F lv) st).1 = hs.foldl (BS.step F lv) st.1
  | [], _, hs => ⟨hs, rfl⟩
  | h :: hs, st, hst => by
    obtain ⟨h1, h2⟩ := stepM_ok F lv h hst
    obtain ⟨h3, h4⟩ := foldl_stepM_ok F lv hs _ h1
    exact ⟨h3, by rw [List.foldl_cons, List.foldl_cons, h4, h2]⟩

theorem runM_ok (F : Nat → Nat → Nat) (lv : List Nat) (n r : Nat) :
    MaskOK (runM F lv n r) ∧ (runM F lv n r).1 = BS.run F lv n r := by
  have h0 : MaskOK ((⟨[r], [0], [0]⟩ : BS), Nat.shiftLeft 1 r) := by
    intro q
    change (Nat.shiftLeft 1 r).testBit q = decide (q ∈ [r])
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
    simp [eq_comm]
  unfold runM
  rw [rgFold_eq]
  exact foldl_stepM_ok F lv (List.range n) _ h0

theorem runM_fst (F : Nat → Nat → Nat) (lv : List Nat) (n r : Nat) :
    (runM F lv n r).1 = BS.run F lv n r := (runM_ok F lv n r).2

theorem rgRunK_eq (r : Nat) : rgRunK r = rgRun r := by
  rw [rgRunK, rgRun]
  exact runM_fst PGF (List.range 13) 891 r

theorem cover_of_mask {a b c d n v : Nat}
    (h : Nat.beq (Nat.lor (Nat.lor a b) (Nat.lor c d)) (Nat.sub (Nat.shiftLeft 1 n) 1) = true)
    (hv : v < n) : ((a.testBit v || b.testBit v) || (c.testBit v || d.testBit v)) = true := by
  have hb := congrArg (fun x => Nat.testBit x v) (Nat.eq_of_beq_eq_true h)
  simp only [Nat.lor_eq, Nat.testBit_or, Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.one_mul,
    Nat.sub_eq, Nat.testBit_two_pow_sub_one, hv, decide_true] at hb
  exact hb

theorem rgRunsK_eq : rgRunsK = rgRuns := by
  simp only [rgRunsK, rgRuns, rgRunK_eq]

theorem idxK_eq (y : Nat) : ∀ (l : List Nat), idxK y l = l.idxOf y
  | [] => rfl
  | x :: xs => by
    change Bool.rec (motive := fun _ => Nat) (Nat.succ (idxK y xs)) 0 (Nat.beq x y) = _
    rw [List.idxOf_cons, idxK_eq y xs]
    by_cases h : x = y
    · subst h
      simp
    · have hb : Nat.beq x y = false := by
        cases e : Nat.beq x y
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) h
      rw [hb]
      simp [h]

theorem propLFK_eq (F : Nat → Nat → Nat) (s : BS) (c : Nat) :
    ∀ f k, propLFK F s c f k = propLF F s c f k
  | 0, _ => rfl
  | f + 1, k => by
    change Bool.rec (motive := fun _ => Nat) c (F (getK s.lab k) (propLFK F s c f (getK s.par k)))
      (Bool.and (Nat.blt 0 k) (Nat.blt (getK s.par k) k)) = _
    rw [propLF, getK_eq, getK_eq, propLFK_eq F s c f]
    by_cases h : 0 < k ∧ s.par.getD k 0 < k
    · rw [if_pos h, (Nat.blt_eq.mpr h.1 : Nat.blt 0 k = true),
        (Nat.blt_eq.mpr h.2 : Nat.blt (s.par.getD k 0) k = true)]
      rfl
    · rw [if_neg h]
      have hb : Bool.and (Nat.blt 0 k) (Nat.blt (s.par.getD k 0) k) = false := by
        cases h1 : Nat.blt 0 k <;> cases h2 : Nat.blt (s.par.getD k 0) k
        · rfl
        · rfl
        · rfl
        · exact absurd ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2⟩ h
      rw [hb]

theorem candTwK_eq (F : Nat → Nat → Nat) (m : Nat) (s : BS) : candTwK F m s = candTw F m s := by
  funext c
  simp only [candTwK, candTw, propL, getK_eq, idxK_eq, propLFK_eq]

theorem rgMask_bit (r q : Nat) : (rgMask r).testBit q = decide (q ∈ (rgRun r).pts) := by
  rw [rgMask, (runM_ok _ _ _ _).1 q, runM_fst]
  rfl

def ObOK (st' : Nat × List BS) (st : List Nat × List BS) : Prop :=
  (∀ q, st'.1.testBit q = decide (q ∈ st.1)) ∧ st'.2 = st.2

theorem foldl_obStep_ok (F : Nat → Nat → Nat) (m n : Nat) :
    ∀ (rs : List Nat) (st' : Nat × List BS) (st : List Nat × List BS), ObOK st' st →
      ObOK (rs.foldl (obStep F m n) st') (rs.foldl (fun st r => if st.1.contains r then st else
        (st.1 ++ (BS.run F (List.range m) n r).pts, st.2 ++ [BS.run F (List.range m) n r])) st)
  | [], _, _, h => h
  | r :: rs, st', st, h => by
    rw [List.foldl_cons, List.foldl_cons]
    apply foldl_obStep_ok F m n rs
    unfold obStep
    rw [bit_test, h.1 r]
    by_cases hr : r ∈ st.1
    · have hc : st.1.contains r = true := List.contains_iff_mem.mpr hr
      simp only [hr, decide_true, hc, if_true]
      exact h
    · have hc : st.1.contains r = false := by
        cases e : st.1.contains r
        · rfl
        · exact absurd (List.contains_iff_mem.mp e) hr
      simp only [hr, decide_false, hc]
      obtain ⟨hm, hp⟩ := runM_ok F (List.range m) n r
      refine ⟨fun q => ?_, ?_⟩
      · rw [Nat.lor_eq, Nat.testBit_or, h.1 q, hm q, hp]
        simp [List.mem_append]
      · rw [h.2, hp]
        rfl

theorem orbitBSM_eq (F : Nat → Nat → Nat) (m n : Nat) : orbitBSM F m n = orbitBS F m n := by
  unfold orbitBSM orbitBS
  exact (foldl_obStep_ok F m n (List.range n) _ _ ⟨fun q => by simp, rfl⟩).2

theorem rg_parts :
    (orbitBS PGF 13 891).map (fun s => s.pts.headD 0) = [0, 1, 12, 159] ∧
    rgRuns.map (fun s => s.pts.length) = [1, 336, 512, 42] ∧
    (∀ v < 891, ∃ s ∈ rgRuns, v ∈ s.pts) ∧
    (rgRun 0).pts.tail = [] ∧
    (rgRun 1).pts.tail.filter (candTw PGF 13 (rgRun 1)) = [] ∧
    (rgRun 12).pts.tail.filter (candTw PGF 13 (rgRun 12)) = [] ∧
    (rgRun 159).pts.tail.filter (candTw PGF 13 (rgRun 159)) = [590] ∧
    interK (combinedTw PGF rgRuns [0, 1, 12, 590] 1) (combinedTw PGF rgRuns [0, 1, 12, 590] 588) ≠
      interK 1 588 ∧
    ∀ s < 13, nodupM ((List.range 891).map (PGE s)) 0 = true := by
  have h1 := rg_roots
  have h2 := rg_sizes
  have h3 := rg_cover
  have h4 := rg_root0
  have h5 := rg_cand1
  have h6 := rg_cand12
  have h7 := rg_cand159
  have h8 := rg_sep
  rw [orbitBSM_eq] at h1
  rw [rgRunsK_eq] at h2 h8
  rw [candTwK_eq] at h5 h6 h7
  rw [rgRunK_eq] at h4 h5 h6 h7
  refine ⟨beq_iff_eq.1 h1, beq_iff_eq.1 h2, fun v hv => ?_, beq_iff_eq.1 h4,
    beq_iff_eq.1 h5, beq_iff_eq.1 h6, beq_iff_eq.1 h7, bne_iff_ne.1 h8,
    fun s hs => ball_range rg_nodup s hs⟩
  have hb := cover_of_mask h3 hv
  simp only [rgMask_bit, Bool.or_eq_true, decide_eq_true_eq] at hb
  unfold rgRuns
  rcases hb with (hb | hb) | (hb | hb)
  · exact ⟨_, List.mem_cons_self, hb⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hb⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hb⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)), hb⟩

theorem planeDTabs_get : (planeDTabs ()).size = 13 ∧ ∀ s < 13, ((planeDTabs ())[s]!).size = 891 ∧
    ∀ i < 891, ((planeDTabs ())[s]!)[i]! = PGE s i := by
  obtain ⟨h0, h1⟩ := planeTabs_get
  unfold planeDTabs
  refine ⟨by simp [h0], fun s hs => ?_⟩
  have e : ((planeTabs ()).extract 0 13)[s]! = (planeTabs ())[s]! := by
    rw [getElem!_pos _ _ (by simp [h0]; omega), getElem!_pos _ _ (by omega), Array.getElem_extract]
    simp
  rw [e]
  exact h1 s (by omega)

theorem PGF_eq {l x : Nat} (hl : l < 13) : PGF l x = PGE l x := by
  unfold PGF
  rw [(Nat.blt_eq.mpr hl : Nat.blt l 13 = true)]

theorem PGF_lt (l : Nat) {x : Nat} (hx : x < 891) : PGF l x < 891 := by
  by_cases hl : l < 13
  · rw [PGF_eq hl]
    exact pg_lt (by omega) hx
  · unfold PGF
    rw [(Bool.eq_false_iff.mpr fun e => hl (Nat.blt_eq.mp e) : Nat.blt l 13 = false)]
    exact (by decide : (0 : Nat) < 891)

theorem letters_size : (toTables (planeDTabs ())).size = 13 := by
  unfold toTables
  rw [Array.size_map, planeDTabs_get.1]

theorem letters_ap {l x : Nat} (hl : l < (toTables (planeDTabs ())).size) (hx : x < 891) :
    ap (toTables (planeDTabs ()))[l]! x = PGF l x := by
  rw [letters_size] at hl
  obtain ⟨-, h⟩ := planeDTabs_get
  obtain ⟨h1, h2⟩ := h l hl
  unfold toTables ap
  rw [getElem!_pos _ l (by simp [planeDTabs_get.1]; exact hl), Array.getElem_map,
    ← getElem!_pos _ l (by rw [planeDTabs_get.1]; exact hl),
    getElem!_pos _ x (by simp [h1]; exact hx), Array.getElem_map,
    ← getElem!_pos _ x (by rw [h1]; exact hx), h2 x hx, PGF_eq hl, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.lt_trans (pg_lt (by omega) hx) (by decide))]

theorem letters_ap' {l x : Nat} (hl : l < 13) (hx : x < 891) :
    ap (toTables (planeDTabs ()))[l]! x = PGF l x :=
  letters_ap (by rw [letters_size]; exact hl) hx

theorem rgRun_ok {r : Nat} (hr : r < 891) : RunOK 891 PGF (List.range 13) r (rgRun r) :=
  run_ok (fun l _ x hx => PGF_lt l hx) hr

theorem rgRun_closed {r : Nat} (hr : r < 891) :
    ∀ p ∈ (rgRun r).pts, ∀ l < 13, PGF l p ∈ (rgRun r).pts :=
  fun p hp l hl => run_closed (fun l _ x hx => PGF_lt l hx) hr p hp l (List.mem_range.2 hl)

theorem orbitBS_runs (F : Nat → Nat → Nat) (m n : Nat) (hF : ∀ l, ∀ x < n, F l x < n) :
    ∀ s ∈ orbitBS F m n, s = BS.run F (List.range m) n (s.pts.headD 0) := by
  have key : ∀ (rs : List Nat), (∀ r ∈ rs, r < n) → ∀ (st : List Nat × List BS),
      (∀ s ∈ st.2, s = BS.run F (List.range m) n (s.pts.headD 0)) →
      ∀ s ∈ (rs.foldl (fun st r => if st.1.contains r then st else
        (st.1 ++ (BS.run F (List.range m) n r).pts, st.2 ++ [BS.run F (List.range m) n r])) st).2,
        s = BS.run F (List.range m) n (s.pts.headD 0) := by
    intro rs
    induction rs with
    | nil => intro _ st h; exact h
    | cons r rs ih =>
      intro hrs st h
      rw [List.foldl_cons]
      apply ih (fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'))
      split
      · exact h
      · intro s hs
        rcases List.mem_append.1 hs with hs | hs
        · exact h s hs
        · rw [List.mem_singleton] at hs
          subst hs
          have hok := run_ok (lv := List.range m) (fun l _ x hx => hF l x hx)
            (hrs r List.mem_cons_self)
          have hroot := hok.root
          have key : ∀ l : List Nat, l.getD 0 0 = r → l.headD 0 = r := by
            intro l hl
            cases l <;> simpa using hl
          rw [key _ hroot]
  exact key (List.range n) (fun r hr => List.mem_range.1 hr) _ (fun s hs => by simp at hs)

theorem orbitBS_rg : orbitBS PGF 13 891 = rgRuns := by
  have h := orbitBS_runs PGF 13 891 (fun l x hx => PGF_lt l hx)
  have e : orbitBS PGF 13 891 = (orbitBS PGF 13 891).map
      (fun s => BS.run PGF (List.range 13) 891 (s.pts.headD 0)) := by
    conv => lhs; rw [← List.map_id (orbitBS PGF 13 891)]
    exact List.map_congr_left h
  rw [e]
  have e2 : (orbitBS PGF 13 891).map (fun s => BS.run PGF (List.range 13) 891 (s.pts.headD 0)) =
      ((orbitBS PGF 13 891).map (fun s => s.pts.headD 0)).map rgRun := by
    rw [List.map_map]
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply, rgRun]
  rw [e2, rg_parts.1]
  unfold rgRuns
  simp only [List.map_cons, List.map_nil]

theorem orbitTrees_rg : orbitTrees 891 (toTables (planeDTabs ())) = rgRuns.map (treeOf 891) := by
  rw [orbitTrees_eq (by decide) (fun l hl x hx => letters_ap hl hx) (fun l x hx => PGF_lt l hx),
    letters_size, orbitBS_rg]

theorem mem_rgRuns {s : BS} (hs : s ∈ rgRuns) : ∃ r, r < 891 ∧ s = rgRun r := by
  unfold rgRuns at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h
  · exact ⟨0, by decide, h⟩
  · exact ⟨1, by decide, h⟩
  · exact ⟨12, by decide, h⟩
  · exact ⟨159, by decide, h⟩

theorem nodupM_spec : ∀ (l : List Nat) (m : Nat), nodupM l m = true →
    l.Nodup ∧ ∀ x ∈ l, m.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil⟩
  | x :: xs, m, h => by
    have h' : Bool.rec false (nodupM xs (Nat.lor m (Nat.shiftLeft 1 x)))
        (Nat.beq (Nat.land (Nat.shiftRight m x) 1) 0) = true := h
    cases hb : Nat.beq (Nat.land (Nat.shiftRight m x) 1) 0
    · rw [hb] at h'
      exact absurd h' Bool.false_ne_true
    · rw [hb] at h'
      obtain ⟨hnd, hm⟩ := nodupM_spec xs _ h'
      have bit : ∀ y, (Nat.lor m (Nat.shiftLeft 1 x)).testBit y = (m.testBit y || decide (y = x)) :=
        fun y => testBit_lor_bit m x y
      have hx : m.testBit x = false := by
        have e := Nat.eq_of_beq_eq_true hb
        rw [Nat.land_eq, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at e
        rw [Nat.testBit_eq_decide_div_mod_eq, e]
        decide
      refine ⟨List.nodup_cons.2 ⟨fun hmem => ?_, hnd⟩, fun y hy => ?_⟩
      · have := hm x hmem
        rw [bit] at this
        simp at this
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact hx
        · have := hm y hy
          rw [bit, Bool.or_eq_false_iff] at this
          exact this.1

theorem pge_inj {s : Nat} (hs : s < 13) {i j : Nat} (hi : i < 891) (hj : j < 891)
    (e : PGE s i = PGE s j) : i = j := by
  have hnd := (nodupM_spec _ 0 (rg_parts.2.2.2.2.2.2.2.2 s hs)).1
  exact List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) e

theorem tables_toNat {l : Nat} (hl : l < 13) {j : Nat} (hj : j < 891) :
    (((toTables (planeDTabs ()))[l]!)[j]!).toNat = PGF l j :=
  letters_ap' hl hj

theorem invOK_twin {l : Nat} (hl : l < 13) :
    invOK 891 (toTables (planeDTabs ()))[l]! (invT 891 (toTables (planeDTabs ()))[l]!) = true := by
  have hlt : ∀ i < 891, (((toTables (planeDTabs ()))[l]!)[i]!).toNat < 891 := fun i hi => by
    rw [tables_toNat hl hi]
    exact PGF_lt l hi
  have hinj : ∀ i < 891, ∀ j < 891, (((toTables (planeDTabs ()))[l]!)[i]!).toNat =
      (((toTables (planeDTabs ()))[l]!)[j]!).toNat → i = j := by
    intro i hi j hj e
    rw [tables_toNat hl hi, tables_toNat hl hj, PGF_eq hl, PGF_eq hl] at e
    exact pge_inj hl hi hj e
  obtain ⟨-, hval⟩ := invT_loop _ hlt hinj 891 (Nat.le_refl _)
  unfold invOK
  rw [allIn_iff']
  intro i _ hi
  unfold ap
  rw [invT_eq_foldl, hval i hi, toNat_ofNat_of_lt (by omega)]
  simp

theorem tablesOK_true : tablesOK 891 (planeDTabs ()) = true := by
  obtain ⟨hsz, hget⟩ := planeDTabs_get
  unfold tablesOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true, beq_iff_eq]
  refine ⟨⟨by decide, fun i hi => ?_⟩, fun i hi => ?_⟩
  · rw [hsz] at hi
    obtain ⟨h1, h2⟩ := hget i hi
    rw [← getElem!_pos _ i (by rw [hsz]; exact hi)]
    refine ⟨h1, fun j hj => ?_⟩
    rw [h1] at hj
    rw [← getElem!_pos _ j (by rw [h1]; exact hj), h2 j hj]
    simpa using pg_lt (by omega) hj
  · rw [letters_size] at hi
    rw [← getElem!_pos _ i (by rw [letters_size]; exact hi)]
    exact invOK_twin hi

theorem interAux_eq {a b : Nat} (ha : a < 891) (hb : b < 891) : ∀ k ≤ 24,
    interAux (planeXData ()) a b k =
      ((List.range k).filter fun m => (List.range 24).any fun j => PXE b j == PXE a m).length
  | 0, _ => rfl
  | k + 1, hk => by
    rw [interAux, interAux_eq ha hb k (by omega), List.range_succ (n := k), List.filter_append,
      List.length_append]
    congr 1
    have e : memRow (planeXData ())[b]! ((planeXData ())[a]!)[k]! =
        (List.range 24).any fun j => PXE b j == PXE a k := by
      apply Bool.eq_iff_iff.mpr
      rw [memRow_iff, List.any_eq_true, px_get ha (by omega)]
      constructor
      · rintro ⟨j, hj, he⟩
        exact ⟨j, List.mem_range.2 hj, by rw [← px_get hb hj, he]; simp⟩
      · rintro ⟨j, hj, he⟩
        exact ⟨j, List.mem_range.1 hj, by rw [px_get hb (List.mem_range.1 hj)]; simpa using he⟩
    rw [e]
    simp only [List.filter_cons, List.filter_nil]
    by_cases h : ((List.range 24).any fun j => PXE b j == PXE a k) = true
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl

theorem planeInterCount_eq {a b : Nat} (ha : a < 891) (hb : b < 891) :
    planeInterCount (planeXData ()) a b = interK a b :=
  interAux_eq ha hb 24 (Nat.le_refl _)

theorem combinedTw_lt {F : Nat → Nat → Nat} {n : Nat} (hF : ∀ l, ∀ x < n, F l x < n) {v : Nat}
    (hv : v < n) : ∀ (ss : List BS) (cs : List Nat), (∀ c ∈ cs, c < n) → combinedTw F ss cs v < n
  | [], _, _ => by cases ‹List Nat› <;> exact hv
  | _ :: _, [], _ => hv
  | s :: ss, c :: cs, hcs => by
    unfold combinedTw
    split
    · exact propLF_lt hF (hcs c List.mem_cons_self) _ _
    · exact combinedTw_lt hF hv ss cs fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')

theorem rgRun_root {r : Nat} (hr : r < 891) : (rgRun r).pts = r :: (rgRun r).pts.tail := by
  have hok := rgRun_ok hr
  have hpos := hok.pos
  have hroot := hok.root
  cases h : (rgRun r).pts with
  | nil => rw [h] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
  | cons a t =>
    rw [h] at hroot
    simp only [List.getD_cons_zero] at hroot
    rw [hroot]
    rfl

theorem tabF_rg {l x : Nat} (hl : l ∈ List.range 13) (hx : x < 891) :
    tabF (toTables (planeDTabs ())) l x = PGF l x :=
  letters_ap' (List.mem_range.1 hl) hx

theorem rgRun_tabF {r : Nat} (hr : r < 891) :
    rgRun r = BS.run (tabF (toTables (planeDTabs ()))) (List.range 13) 891 r :=
  CFSG.KS.RouteP.run_congr hr (fun l _ x hx => PGF_lt l hx) (fun l hl x hx => (tabF_rg hl hx).symm)

theorem treeOK_rg {r : Nat} (hr : r < 891) :
    treeOK 891 (ap (treeOf 891 (rgRun r)).pts 0) (treeOf 891 (rgRun r)) (toTables (planeDTabs ()))
      (Array.range (planeDTabs ()).size) = true := by
  have hF : ∀ l ∈ List.range 13, ∀ x < 891, tabF (toTables (planeDTabs ())) l x < 891 :=
    fun l hl x hx => by rw [tabF_rg hl hx]; exact PGF_lt l hx
  have hok := run_ok hF hr
  have hcl := run_closed hF hr
  rw [← rgRun_tabF hr] at hok hcl
  rw [treeOf_pts_ap (by decide) hok, hok.root, planeDTabs_get.1, array_range_eq]
  exact treeOK_treeOf (by decide) hok hcl (fun l hl => by have := List.mem_range.1 hl; omega)

theorem candList_rg {r : Nat} (hr : r < 891) :
    candList (toTables (planeDTabs ())) (treeOf 891 (rgRun r)) =
      r :: (rgRun r).pts.tail.filter (candTw PGF 13 (rgRun r)) := by
  rw [candList_treeOf (by decide) (letters_size ▸ rgRun_ok hr)
    (fun p hp l hl => rgRun_closed hr p hp l (letters_size ▸ hl)) (fun l hl x hx => letters_ap hl hx)
    (fun l x hx => PGF_lt l hx) (by rw [letters_size]; decide) (by rw [letters_size]; decide),
    letters_size, rgRun_root hr, List.filter_cons_of_pos (candTw_root (rgRun_ok hr) (rgRun_closed hr))]
  rw [← rgRun_root hr]

theorem allIn_false {lo hi : Nat} {p : Nat → Bool} {i : Nat} (h1 : lo ≤ i) (h2 : i < hi)
    (h : p i = false) : allIn lo hi p = false := by
  rw [Bool.eq_false_iff]
  intro ha
  rw [allIn_iff'.1 ha i h1 h2] at h
  exact Bool.noConfusion h

theorem rigidOK_planeDTabs : rigidOK 891 (planeDTabs ()) (planeInterCount (planeXData ())) = true := by
  obtain ⟨-, hsz, hcov, h0, hc1, hc12, hc159, hsep, -⟩ := rg_parts
  have hruns : ∀ s ∈ rgRuns, ∃ r, RunOK 891 PGF (List.range (toTables (planeDTabs ())).size) r s := by
    intro s hs
    obtain ⟨r, hr, e⟩ := mem_rgRuns hs
    rw [e, letters_size]
    exact ⟨r, rgRun_ok hr⟩
  have hcomb : ∀ cs : List Nat, (∀ c ∈ cs, c < 891) → ∀ v < 891,
      combined (toTables (planeDTabs ())) (rgRuns.map (treeOf 891)) cs v =
        combinedTw PGF rgRuns cs v :=
    fun cs hcs v hv => combined_treeOf (by decide) (fun l hl x hx => letters_ap hl hx)
      (fun l x hx => PGF_lt l hx) (by rw [letters_size]; decide) (by rw [letters_size]; decide)
      hv rgRuns cs hruns hcs
  unfold rigidOK rigidOKAt
  simp only [tablesOK_true, orbitTrees_rg, Bool.true_and, Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro T hT
    obtain ⟨s, hs, e1⟩ := List.mem_map.1 hT
    obtain ⟨r, hr, e2⟩ := mem_rgRuns hs
    rw [← e1, e2]
    exact treeOK_rg hr
  · rw [allIn_iff']
    intro v _ hv
    obtain ⟨s, hs, hm⟩ := hcov v hv
    obtain ⟨r, hr, e⟩ := mem_rgRuns hs
    rw [e] at hs hm
    rw [List.any_eq_true]
    exact ⟨treeOf 891 (rgRun r), List.mem_map.2 ⟨_, hs, rfl⟩,
      by rw [inTree_treeOf (by decide) (rgRun_ok hr) hv]; exact List.contains_iff_mem.mpr hm⟩
  · have e : (rgRuns.map (treeOf 891)).map (fun T => T.pts.size) = [1, 336, 512, 42] := by
      rw [List.map_map, ← hsz]
      apply List.map_congr_left
      intro s _
      exact treeOf_size
    rw [e]
    decide
  · have e : (rgRuns.map (treeOf 891)).map (fun T => T.pts.size) = [1, 336, 512, 42] := by
      rw [List.map_map, ← hsz]
      apply List.map_congr_left
      intro s _
      exact treeOf_size
    rw [e]
    decide
  · have hroots : (rgRuns.map (treeOf 891)).map (fun T => ap T.pts 0) = [0, 1, 12, 159] := by
      simp only [rgRuns, List.map_cons, List.map_nil]
      rw [treeOf_pts_ap (by decide) (rgRun_ok (by decide)), treeOf_pts_ap (by decide) (rgRun_ok (by decide)),
        treeOf_pts_ap (by decide) (rgRun_ok (by decide)), treeOf_pts_ap (by decide) (rgRun_ok (by decide)),
        (rgRun_ok (by decide : 0 < 891)).root, (rgRun_ok (by decide : 1 < 891)).root,
        (rgRun_ok (by decide : 12 < 891)).root, (rgRun_ok (by decide : 159 < 891)).root]
    have hcands : (rgRuns.map (treeOf 891)).map (candList (toTables (planeDTabs ()))) =
        [[0], [1], [12], [159, 590]] := by
      simp only [rgRuns, List.map_cons, List.map_nil]
      rw [candList_rg (by decide), candList_rg (by decide), candList_rg (by decide),
        candList_rg (by decide), hc1, hc12, hc159, h0]
      simp
    rw [hroots, hcands]
    simp only [allSections, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true, beq_iff_eq]
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true]
    refine ⟨Or.inl (beq_self_eq_true _), Or.inr ?_⟩
    rw [Bool.not_eq_true']
    unfold preservesR
    apply allIn_false (i := 1) (by decide) (by decide)
    apply allIn_false (i := 588) (by decide) (by decide)
    rw [beq_eq_false_iff_ne]
    have hcs : ∀ c ∈ [0, 1, 12, 590], c < 891 := by decide
    rw [getElem!_pos _ 1 (by simp), Array.getElem_ofFn, getElem!_pos _ 588 (by simp),
      Array.getElem_ofFn]
    simp only []
    rw [hcomb _ hcs 1 (by decide), hcomb _ hcs 588 (by decide),
      planeInterCount_eq (combinedTw_lt (fun l x hx => PGF_lt l hx) (by decide) _ _ hcs)
        (combinedTw_lt (fun l x hx => PGF_lt l hx) (by decide) _ _ hcs),
      planeInterCount_eq (by decide) (by decide)]
    exact hsep

end CertificateChecks.KernelRouteP


module

public import Certificates.Kernel.SporSch.Ru.R7046K
public import Certificates.Kernel.SporSch.Ru.E7046K
public import Certificates.Kernel.SporSch.Ru.F7046K
public import Certificates.Kernel.SporSch.Ru.Glue7045
public import Certificates.Kernel.SporSch.Ru.Q7305
import Certificates.Kernel.SporSch.Ru.JFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Glue7046

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab CFSG.KS.RowTree
  CFSG.KS.RuTree CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.G2Ru7164 CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

theorem orB_eq (a b : Bool) : CFSG.KLC.Fi22.orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KLC.Fi22.notB a = !a := by cases a <;> rfl

theorem eqB_eq (a b : Bool) : S7046.eqB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem orbCheck_of {n kG m : Nat} {gens : Array (Array Nat)} {g : Nat → Nat → Nat}
    {L R P K D Q ORD FO DEP PAR GI : Nat → Nat}
    (hkG : 0 < kG) (hs : gens.size = kG) (hg : ∀ k < kG, ∀ x < n, (gens[k]!)[x]! = g k x)
    (hrec : orbRecK n m kG g L R P K D = true)
    (hqr : CFSG.KLC.Fi22.andB (Nat.ble m n) (allN m (fun t => Nat.beq (Q t) (R t))) = true)
    (hf : allN n (forestAtG n kG m g Q ORD FO DEP PAR GI) = true)
    (he : allN (kG * n) (eventAtG n kG m g Q ORD FO) = true)
    (hp : allN n (partAtG n kG m g L Q DEP PAR GI) = true)
    (hk : allN m (rootAtG n L Q) = true) : orbCheck n gens = true := by
  obtain ⟨r1, r2⟩ := orbRoots_of_K hs hg hrec
  obtain ⟨-, l2⟩ := orbLabels_of_K hs hg hrec
  obtain ⟨h1, h2⟩ := andB_iff'.1 hqr
  unfold orbCheck
  exact orbitPartOK_forestKG hkG hs hg
    ⟨r1, fun t ht => by rw [r2 t ht, Nat.eq_of_beq_eq_true (allN_spec h2 t ht)]⟩
    (Nat.ble_eq.mp h1) l2 (fun t ht => allN_spec hf t ht) (fun e he' => allN_spec he e he')
    (fun x hx => allN_spec hp x hx) (fun c hc => allN_spec hk c hc)

theorem hgR : ∀ k < 4, ∀ x < 4060, (ruR0Arrs[k]!)[x]! = Q7307.gR k x := fun k hk x hx => by
  unfold ruR0Arrs
  rw [getElem!_ofFn_of_lt _ hk]
  change (ruR0Arr k)[x]! = _
  rw [Iso7047.r_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
  rfl

theorem hgE : ∀ k < 2, ∀ x < 4060, (ruEGArrs[k]!)[x]! = Q7305.gE k x := fun k hk x hx => by
  unfold ruEGArrs
  rw [getElem!_ofFn_of_lt _ hk]
  change (ruEGArr k)[x]! = _
  rw [Q7305.eg_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
  rfl

theorem fg_eq {i : Nat} (hi : i < 2) : ruFGArr i = unpack 4060 12 (Q7046F.F i) := by
  rw [ruFGArr, Q7046F.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Q7046F.all i hi

theorem hgF : ∀ k < 2, ∀ x < 4060, (ruFGArrs[k]!)[x]! = F7046.gF k x := fun k hk x hx => by
  unfold ruFGArrs
  rw [getElem!_ofFn_of_lt _ hk]
  change (ruFGArr k)[x]! = _
  rw [fg_eq hk, CFSG.KC.BfsPin.unpack_get' hx]
  rfl

theorem flab_get {y : Nat} (hy : y < 4060) : ruFLab[y]! = F7046.Lf y := by
  have hs : ruFGArrs.size = 2 := by simp [ruFGArrs]
  exact (orbLabels_of_K hs hgF F7046.kOrb).2 y hy

theorem flab_lt {y : Nat} (hy : y < 4060) : F7046.Lf y < 8 := by
  have := allN_spec F7046.kLt y hy
  simpa using this

theorem orbR : orbCheck 4060 ruR0Arrs = true :=
  orbCheck_of (by norm_num) (by simp [ruR0Arrs]) hgR Q7307.kOrb R7046.kQR R7046.kF R7046.kE
    R7046.kP R7046.kRt

theorem orbE : orbCheck 4060 ruEGArrs = true :=
  orbCheck_of (by norm_num) (by simp [ruEGArrs]) hgE Q7305.kOrbE E7046.kQR E7046.kF E7046.kE
    E7046.kP E7046.kRt

theorem orbF : orbCheck 4060 ruFGArrs = true :=
  orbCheck_of (by norm_num) (by simp [ruFGArrs]) hgF F7046.kOrb F7046.kQR F7046.kF F7046.kE
    F7046.kP F7046.kRt

theorem labCount_eq (c : Nat) : ∀ n, n ≤ 4060 → labCount n ruQLab c = R7046.cntL n c
  | 0, _ => rfl
  | n + 1, hn => by
    have e1 : labCount (n + 1) ruQLab c =
        labCount n ruQLab c + if (ruQLab[n]! == c) = true then 1 else 0 := by
      simp [labCount, List.range_succ, List.countP_append]
    change _ = Bool.rec (motive := fun _ => Nat) (R7046.cntL n c) (Nat.succ (R7046.cntL n c))
      (Nat.beq (Q7307.Lf n) c)
    rw [e1, labCount_eq c n (by omega), Q7307.qlab_get (by omega), Q7307.nat_beq]
    cases h : Nat.beq (Q7307.Lf n) c <;> simp

theorem hg0 : ruG0 = 2808 := rfl

theorem q_ok : orbCheck 4060 ruR0Arrs = true ∧
    (allLt 4060 fun x => x == 0 || ruQLab[x]! != ruQLab[0]!) = true ∧
    (allLt 1755 fun j => ruQLab[ruDArr[j]!]! == ruQLab[1]!) = true ∧
    labCount 4060 ruQLab ruQLab[1]! = 1755 ∧ labCount 4060 ruQLab ruQLab[ruG0]! = 2304 ∧
    (allLt 4060 fun x => ruQLab[x]! == ruQLab[0]! || ruQLab[x]! == ruQLab[1]! ||
      ruQLab[x]! == ruQLab[ruG0]!) = true ∧
    ruQLab[1]! ≠ ruQLab[ruG0]! ∧ ruQLab[0]! ≠ ruQLab[ruG0]! ∧
    isInvA 4060 (ruTreeArr 1) ruTI1 = true ∧ isInvA 4060 (ruTreeArr ruG0) ruTIG0 = true := by
  have q0 := Q7307.qlab_get (y := 0) (by norm_num)
  have q1 := Q7307.qlab_get (y := 1) (by norm_num)
  have qg := Q7307.qlab_get (y := 2808) (by norm_num)
  obtain ⟨c1, c2⟩ := andB_iff'.1 R7046.kQC
  obtain ⟨n1, n2⟩ := andB_iff'.1 R7046.kQne
  have n1' : Q7307.Lf 1 ≠ Q7307.Lf 2808 := fun e => by
    rw [e, notB_eq, Nat.beq_refl] at n1
    exact absurd n1 (by decide)
  have n2' : Q7307.Lf 0 ≠ Q7307.Lf 2808 := fun e => by
    rw [e, notB_eq, Nat.beq_refl] at n2
    exact absurd n2 (by decide)
  refine ⟨orbR, CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_,
    CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_, ?_, ?_, CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_,
    ?_, ?_, Glue7045.isInv_tree (x := 1) (by norm_num), Glue7045.isInv_tree (x := 2808) (by norm_num)⟩
  · have h := allN_spec R7046.kQ0 x hx
    simp only [orB_eq, notB_eq, ← Q7307.nat_beq] at h
    rw [Q7307.qlab_get hx, q0]
    exact h
  · obtain ⟨dj, djl, -⟩ := Iso7047.d_get hj
    have h := allN_spec R7046.kQD j hj
    rw [dj, Q7307.qlab_get djl, q1, Q7307.nat_beq]
    exact h
  · rw [q1, labCount_eq _ 4060 le_rfl]
    exact Nat.eq_of_beq_eq_true c1
  · rw [hg0, qg, labCount_eq _ 4060 le_rfl]
    exact Nat.eq_of_beq_eq_true c2
  · have h := allN_spec R7046.kQ3 x hx
    simp only [orB_eq, ← Q7307.nat_beq, ← Bool.or_assoc] at h
    rw [Q7307.qlab_get hx, q0, q1, hg0, qg]
    exact h
  · rw [q1, hg0, qg]
    exact n1'
  · rw [q0, hg0, qg]
    exact n2'

theorem stab_of {a : Array Nat} {G b : Nat} (hb : b < 4060) (hR : a = unpack 4060 12 G)
    (h : S7046.sOK G b = true) :
    (isInvA 4060 a (invCand 4060 a) && ruSift 4060 (ruField4060 3) ruJoinBase a && a[0]! == 0 &&
      a[b]! == b) = true := by
  unfold S7046.sOK at h
  simp only [bAnd_iff] at h
  obtain ⟨hperm, hhi, hrange, hsift, h0, hb'⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨(inv_of hR hperm).2, ?_⟩, ?_⟩, ?_⟩
  · exact siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl hR (Nat.eq_of_beq_eq_true hhi) hrange hsift
  · rw [hR, CFSG.KC.BfsPin.unpack_get' (by norm_num)]
    exact Nat.eq_of_beq_eq_true h0
  · rw [hR, CFSG.KC.BfsPin.unpack_get' hb]
    exact Nat.eq_of_beq_eq_true hb'

theorem stabs_ok : (allLt 2 fun i => isInvA 4060 (ruFGArr i) (invCand 4060 (ruFGArr i)) &&
        ruSift 4060 (ruField4060 3) ruJoinBase (ruFGArr i) && (ruFGArr i)[0]! == 0 &&
        (ruFGArr i)[1]! == 1) = true ∧
      (allLt 2 fun i => isInvA 4060 (ruEGArr i) (invCand 4060 (ruEGArr i)) &&
        ruSift 4060 (ruField4060 3) ruJoinBase (ruEGArr i) && (ruEGArr i)[0]! == 0 &&
        (ruEGArr i)[ruG0]! == ruG0) = true ∧
      orbCheck 4060 ruFGArrs = true ∧ (allLt 4060 fun x => decide (ruFLab[x]! < 8)) = true ∧
      orbCheck 4060 ruEGArrs = true ∧ (allLt 4060 fun x => decide (ruELab[x]! < 9)) = true := by
  refine ⟨CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_, CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_,
    orbF, CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_, orbE,
    CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_⟩
  · have h : S7046.sOK (Q7046F.F i) 1 = true := by
      interval_cases i
      exacts [F7046.kS0, F7046.kS1]
    exact stab_of (by norm_num) (fg_eq hi) h
  · have h : S7046.sOK (Q7305E.F i) 2808 = true := by
      interval_cases i
      exacts [E7046.kS0, E7046.kS1]
    rw [hg0]
    exact stab_of (by norm_num) (Q7305.eg_eq hi) h
  · rw [flab_get hx, decide_eq_true_eq]
    exact flab_lt hx
  · rw [Q7305.elab_get hx, decide_eq_true_eq]
    exact Q7305.elab_lt hx

theorem a0_ok : ruA0A[0]! = 1 ∧ ruA0A[1]! = 0 := by
  obtain ⟨h0, h1⟩ := andB_iff'.1 R7046.kA0
  rw [a0_eq, CFSG.KC.BfsPin.unpack_get' (by norm_num), CFSG.KC.BfsPin.unpack_get' (by norm_num)]
  exact ⟨Nat.eq_of_beq_eq_true h0, Nat.eq_of_beq_eq_true h1⟩

theorem sel_eq {L : Nat → Nat} {m : Nat} (hL : ∀ x < 4060, L x < m) {p : Nat → Bool} :
    ∀ xs : List Nat, (∀ x ∈ xs, x < 4060) →
    xs.countP (fun x => p (L x)) =
      ∑ l ∈ Finset.range m, if p l then xs.countP (fun x => Nat.beq (L x) l) else 0
  | [], _ => by simp
  | x :: xs, h => by
    have ih := sel_eq hL (p := p) xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hlt := hL x (h x List.mem_cons_self)
    simp only [List.countP_cons, ih]
    have e1 : ∀ l ∈ Finset.range m, (if p l then
        (xs.countP (fun x => Nat.beq (L x) l) + if Nat.beq (L x) l = true then 1 else 0) else 0) =
        (if p l then xs.countP (fun x => Nat.beq (L x) l) else 0) +
          (if L x = l then (if p l then 1 else 0) else 0) := fun l _ => by
      by_cases hp : p l <;> by_cases he : L x = l <;> simp [hp, he, Nat.beq_eq]
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_ite_eq,
      if_pos (Finset.mem_range.2 hlt)]

theorem of8 {b : Fin 8 → Bool} {M : Nat} (h0 : bAt b 0 = CFSG.KLC.Fi22.bt M 0) (h1 : bAt b 1 = CFSG.KLC.Fi22.bt M 1)
    (h2 : bAt b 2 = CFSG.KLC.Fi22.bt M 2) (h3 : bAt b 3 = CFSG.KLC.Fi22.bt M 3) (h4 : bAt b 4 = CFSG.KLC.Fi22.bt M 4)
    (h5 : bAt b 5 = CFSG.KLC.Fi22.bt M 5) (h6 : bAt b 6 = CFSG.KLC.Fi22.bt M 6) (h7 : bAt b 7 = CFSG.KLC.Fi22.bt M 7) :
    ∀ l < 8, bAt b l = CFSG.KLC.Fi22.bt M l := by
  intro l hl
  interval_cases l <;> assumption

theorem of9 {b : Fin 9 → Bool} {M : Nat} (h0 : bAt b 0 = CFSG.KLC.Fi22.bt M 0) (h1 : bAt b 1 = CFSG.KLC.Fi22.bt M 1)
    (h2 : bAt b 2 = CFSG.KLC.Fi22.bt M 2) (h3 : bAt b 3 = CFSG.KLC.Fi22.bt M 3) (h4 : bAt b 4 = CFSG.KLC.Fi22.bt M 4)
    (h5 : bAt b 5 = CFSG.KLC.Fi22.bt M 5) (h6 : bAt b 6 = CFSG.KLC.Fi22.bt M 6) (h7 : bAt b 7 = CFSG.KLC.Fi22.bt M 7)
    (h8 : bAt b 8 = CFSG.KLC.Fi22.bt M 8) :
    ∀ l < 9, bAt b l = CFSG.KLC.Fi22.bt M l := by
  intro l hl
  interval_cases l <;> assumption

theorem row1_eq {x : Nat} (hx : x < 4060) (ht : pg 12 (mask 12) Q7307.TI x < 4060) :
    ruRowA ruTI1 x = Nat.beq (Q7307.Lf (Q7307.fl Q7307.TI x)) (Q7307.Lf 1) := by
  unfold ruRowA
  rw [Q7307.ti_eq, CFSG.KC.BfsPin.unpack_get' hx, Q7307.qlab_get ht,
    Q7307.qlab_get (by norm_num), Q7307.nat_beq]
  rfl

theorem f_sel : ∀ b : Fin 8 → Bool, selCount 4060 ruFLab b = 1755 → bAt b ruFLab[0]! = true →
    bAt b ruFLab[1]! = false →
    (allLt 4060 fun x => bAt b ruFLab[x]! == ruRowA ruTI1 x) = true ∨
    (allLt 4060 fun x => !(bAt b ruFLab[x]!) || !(ruInS x)) = true := by
  intro b hsel hb0 hb1
  obtain ⟨w0, w1⟩ := andB_iff'.1 F7046.kW
  rw [flab_get (by norm_num), Nat.eq_of_beq_eq_true w0] at hb0
  rw [flab_get (by norm_num), Nat.eq_of_beq_eq_true w1] at hb1
  have hs : selCount 4060 ruFLab b = (List.range 4060).countP (fun x => bAt b (F7046.Lf x)) := by
    unfold selCount
    apply List.countP_congr
    intro x hx
    rw [flab_get (List.mem_range.1 hx)]
  rw [hs, sel_eq (fun x hx => flab_lt hx) (p := bAt b) _ (fun x hx => List.mem_range.1 hx)] at hsel
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsel
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := F7046.kCnt
  unfold F7046.cnt at c0 c1 c2 c3 c4 c5 c6 c7
  rw [c0, c1, c2, c3, c4, c5, c6, c7, hb0, hb1] at hsel
  have key : (bAt b 2 = true ∧ bAt b 3 = true ∧ bAt b 4 = false ∧ bAt b 5 = false ∧
      bAt b 6 = true ∧ bAt b 7 = true) ∨
      (bAt b 2 = true ∧ bAt b 3 = false ∧ bAt b 4 = true ∧ bAt b 5 = false ∧
      bAt b 6 = true ∧ bAt b 7 = true) := by
    revert hsel
    generalize bAt b 2 = b2
    generalize bAt b 3 = b3
    generalize bAt b 4 = b4
    generalize bAt b 5 = b5
    generalize bAt b 6 = b6
    generalize bAt b 7 = b7
    cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> simp
  rcases key with ⟨k2, k3, k4, k5, k6, k7⟩ | ⟨k2, k3, k4, k5, k6, k7⟩
  · have hm := of8 (M := 205) (hb0.trans rfl) (hb1.trans rfl) (k2.trans rfl) (k3.trans rfl)
      (k4.trans rfl) (k5.trans rfl) (k6.trans rfl) (k7.trans rfl)
    refine Or.inr (CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_)
    have h := allN_spec F7046.kMiss x hx
    simp only [orB_eq, notB_eq] at h
    rw [flab_get hx, hm _ (flab_lt hx), Q7305.inS_eq hx]
    exact h
  · have hm := of8 (M := 213) (hb0.trans rfl) (hb1.trans rfl) (k2.trans rfl) (k3.trans rfl)
      (k4.trans rfl) (k5.trans rfl) (k6.trans rfl) (k7.trans rfl)
    refine Or.inl (CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_)
    have h := F7046.kRow
    rw [Q7307.strictB_eq] at h
    obtain ⟨ht, he⟩ := (bAnd_iff _ _).1 (allN_spec h x hx)
    rw [eqB_eq] at he
    rw [flab_get hx, hm _ (flab_lt hx), row1_eq hx (Nat.blt_eq.mp ht)]
    exact he

theorem e_sel : ∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 1755 → bAt b ruELab[0]! = false →
    bAt b ruELab[ruG0]! = false →
    (allLt 4060 fun x => bAt b ruELab[x]! == ruRowA ruTIG0 x) = true ∨
    (allLt 4060 fun x => bAt b ruELab[x]! == (ruQLab[x]! == ruQLab[1]!)) = true := by
  intro b hsel hb0 hb8
  have w0 : Q7305.ELf 0 = 0 := by
    have h := Q7305.kWit
    simp only [bAnd_iff, Nat.beq_eq] at h
    exact h.1
  rw [Q7305.elab_get (by norm_num), w0] at hb0
  rw [hg0, Q7305.elab_get (by norm_num), Nat.eq_of_beq_eq_true E7046.kW] at hb8
  have hs : selCount 4060 ruELab b = (List.range 4060).countP (fun x => bAt b (Q7305.ELf x)) := by
    unfold selCount
    apply List.countP_congr
    intro x hx
    rw [Q7305.elab_get (List.mem_range.1 hx)]
  rw [hs, sel_eq (fun x hx => Q7305.elab_lt hx) (p := bAt b) _
    (fun x hx => List.mem_range.1 hx)] at hsel
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hsel
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := Q7305.kCnt
  unfold Q7305.cnt at c0 c1 c2 c3 c4 c5 c6 c7 c8
  rw [c0, c1, c2, c3, c4, c5, c6, c7, c8, hb0, hb8] at hsel
  have key : (bAt b 1 = false ∧ bAt b 2 = true ∧ bAt b 3 = true ∧ bAt b 4 = false ∧
      bAt b 5 = false ∧ bAt b 6 = false ∧ bAt b 7 = false) ∨
      (bAt b 1 = true ∧ bAt b 2 = true ∧ bAt b 3 = false ∧ bAt b 4 = false ∧
      bAt b 5 = false ∧ bAt b 6 = false ∧ bAt b 7 = false) := by
    revert hsel
    generalize bAt b 1 = b1
    generalize bAt b 2 = b2
    generalize bAt b 3 = b3
    generalize bAt b 4 = b4
    generalize bAt b 5 = b5
    generalize bAt b 6 = b6
    generalize bAt b 7 = b7
    cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> simp
  rcases key with ⟨k1, k2, k3, k4, k5, k6, k7⟩ | ⟨k1, k2, k3, k4, k5, k6, k7⟩
  · have hm := of9 (M := 12) (hb0.trans rfl) (k1.trans rfl) (k2.trans rfl) (k3.trans rfl)
      (k4.trans rfl) (k5.trans rfl) (k6.trans rfl) (k7.trans rfl) (hb8.trans rfl)
    refine Or.inl (CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_)
    have h := E7046.kN
    rw [Q7307.strictB_eq] at h
    obtain ⟨ht, he⟩ := (bAnd_iff _ _).1 (allN_spec h x hx)
    rw [eqB_eq] at he
    have ht' : Q7307.fl Q7305.TG x < 4060 := Nat.blt_eq.mp ht
    rw [Q7305.elab_get hx, hm _ (Q7305.elab_lt hx), Q7305.row_eq hx ht']
    exact he
  · have hm := of9 (M := 6) (hb0.trans rfl) (k1.trans rfl) (k2.trans rfl) (k3.trans rfl)
      (k4.trans rfl) (k5.trans rfl) (k6.trans rfl) (k7.trans rfl) (hb8.trans rfl)
    refine Or.inr (CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_)
    have h := allN_spec E7046.kD x hx
    rw [eqB_eq] at h
    rw [Q7305.elab_get hx, hm _ (Q7305.elab_lt hx), Q7307.qlab_get hx,
      Q7307.qlab_get (by norm_num), Q7307.nat_beq]
    exact h

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7046 :
    (orbCheck 4060 ruR0Arrs = true ∧
       (allLt 4060 fun x => x == 0 || ruQLab[x]! != ruQLab[0]!) = true ∧
       (allLt 1755 fun j => ruQLab[ruDArr[j]!]! == ruQLab[1]!) = true ∧
       labCount 4060 ruQLab ruQLab[1]! = 1755 ∧ labCount 4060 ruQLab ruQLab[ruG0]! = 2304 ∧
       (allLt 4060 fun x => ruQLab[x]! == ruQLab[0]! || ruQLab[x]! == ruQLab[1]! ||
         ruQLab[x]! == ruQLab[ruG0]!) = true ∧
       ruQLab[1]! ≠ ruQLab[ruG0]! ∧ ruQLab[0]! ≠ ruQLab[ruG0]! ∧
       isInvA 4060 (ruTreeArr 1) ruTI1 = true ∧ isInvA 4060 (ruTreeArr ruG0) ruTIG0 = true)
    ∧ ((allLt 2 fun i => isInvA 4060 (ruFGArr i) (invCand 4060 (ruFGArr i)) &&
         ruSift 4060 (ruField4060 3) ruJoinBase (ruFGArr i) && (ruFGArr i)[0]! == 0 &&
         (ruFGArr i)[1]! == 1) = true ∧
       (allLt 2 fun i => isInvA 4060 (ruEGArr i) (invCand 4060 (ruEGArr i)) &&
         ruSift 4060 (ruField4060 3) ruJoinBase (ruEGArr i) && (ruEGArr i)[0]! == 0 &&
         (ruEGArr i)[ruG0]! == ruG0) = true ∧
       orbCheck 4060 ruFGArrs = true ∧ (allLt 4060 fun x => decide (ruFLab[x]! < 8)) = true ∧
       orbCheck 4060 ruEGArrs = true ∧ (allLt 4060 fun x => decide (ruELab[x]! < 9)) = true)
    ∧ (ruA0A[0]! = 1 ∧ ruA0A[1]! = 0)
    ∧ ((∀ b : Fin 8 → Bool, selCount 4060 ruFLab b = 1755 → bAt b ruFLab[0]! = true →
         bAt b ruFLab[1]! = false →
         (allLt 4060 fun x => bAt b ruFLab[x]! == ruRowA ruTI1 x) = true ∨
         (allLt 4060 fun x => !(bAt b ruFLab[x]!) || !(ruInS x)) = true) ∧
       (∀ b : Fin 9 → Bool, selCount 4060 ruELab b = 1755 → bAt b ruELab[0]! = false →
         bAt b ruELab[ruG0]! = false →
         (allLt 4060 fun x => bAt b ruELab[x]! == ruRowA ruTIG0 x) = true ∨
         (allLt 4060 fun x => bAt b ruELab[x]! == (ruQLab[x]! == ruQLab[1]!)) = true)) := ⟨q_ok, stabs_ok, a0_ok, f_sel, e_sel⟩

end CertificateChecks.KernelSporSch.Glue7046

end

module

public import Certificates.Kernel.S63K.FChecks
public import Certificates.Kernel.S63K.G4235
public import Certificates.Kernel.S63K.H4240
public import CFSG.Certificates.Kernel.S63K.F48Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.F4236

open CFSG.D4Hex CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelS63 CertificateChecks.KernelS63.HD

theorem beqT {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem evalW_eq : ∀ w : List ℕ, f48EvalW permArrs w = hexEvalArr permArrs w
  | [] => rfl
  | l :: w => by
    change compA 819 permArrs[l]! (f48EvalW permArrs w) = compA 819 permArrs[l]! (hexEvalArr permArrs w)
    rw [evalW_eq w]

theorem ev_get {w : List ℕ} (hw : ∀ k ∈ w, k < 8) {x : ℕ} (hx : x < 819) :
    (f48EvalW permArrs w)[x]! = ptW w x ∧ ptW w x < 819 := by
  rw [evalW_eq]
  exact G4235.evalArr_get w hw x hx

theorem wordArrs_get (ws : List (List ℕ)) {j : ℕ} (hj : j < ws.length) :
    (f48WordArrs permArrs ws)[j]! = f48EvalW permArrs (ws.getD j []) := by
  unfold f48WordArrs
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [List.getElem?_eq_getElem hj]

theorem letters : (∀ k ∈ f48NWord, k < 8) ∧ (∀ k ∈ f48QWord, k < 8) ∧
    (∀ j < 2, ∀ k ∈ f48FWords.getD j [], k < 8) ∧ (∀ j < 8, ∀ k ∈ f48BWords.getD j [], k < 8) := by
  decide +kernel

abbrev Fa : Array (Array ℕ) := f48WordArrs permArrs f48FWords

abbrev Ba : Array (Array ℕ) := f48WordArrs permArrs f48BWords

theorem fa_size : Fa.size = 2 := by simp [f48WordArrs, f48FWords]

theorem ba_size : Ba.size = 8 := by simp [f48WordArrs, f48BWords]

theorem hn {x : ℕ} (hx : x < 819) : (f48EvalW permArrs f48NWord)[x]! = FK.nw x ∧ FK.nw x < 819 :=
  ev_get letters.1 hx

theorem hq {x : ℕ} (hx : x < 819) : (f48EvalW permArrs f48QWord)[x]! = FK.qw x ∧ FK.qw x < 819 :=
  ev_get letters.2.1 hx

theorem hF {j x : ℕ} (hj : j < 2) (hx : x < 819) : (Fa[j]!)[x]! = FK.fw j x ∧ FK.fw j x < 819 := by
  rw [wordArrs_get _ (by simpa [f48FWords] using hj)]
  exact ev_get (letters.2.2.1 j hj) hx

theorem hB {j x : ℕ} (hj : j < 8) (hx : x < 819) : (Ba[j]!)[x]! = FK.bw j x ∧ FK.bw j x < 819 := by
  rw [wordArrs_get _ (by simpa [f48BWords] using hj)]
  exact ev_get (letters.2.2.2 j hj) hx

theorem maps_eq {a : Array ℕ} {f : ℕ → ℕ} (h : ∀ x < 819, a[x]! = f x) :
    f48MapsL0 a = FK.mapsF f := by
  unfold f48MapsL0 FK.mapsF
  rw [h 0 (by norm_num), h 1 (by norm_num), h 5 (by norm_num)]

theorem inB_eq {a : Array ℕ} {f : ℕ → ℕ} (h : ∀ x < 819, a[x]! = f x) : f48InB a = FK.inBF f := by
  unfold f48InB FK.inBF
  rw [maps_eq h, h 0 (by norm_num)]

theorem r_parts : FK.O 0 = 71 ∧ FK.Pa 0 = 0 ∧ FK.La 0 = 0 ∧ orbConsK 819 512 FK.O FK.Ps = true := by
  have h := FK.ch4236R
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨beqT h.1, beqT h.2.1, beqT h.2.2.1, h.2.2.2⟩

theorem hC : OCons FK.O FK.Ps 819 512 := G4235.oCons_of r_parts.2.2.2 (by norm_num)

theorem hact : ∀ h < 512, ∀ j < 2,
    (fun j x => (Fa[j]!)[x]!) j (FK.O h) = FK.O (FK.W (2 * h + j)) := by
  intro h hh j hj
  have e := beqT (MatL.allN_iff.1 (MatL.allN_iff.1 FK.ch4236A h hh) j hj)
  rw [← e]
  exact (hF hj (hC.o h hh).1).1

abbrev R : OrbRec := orbBFS 819 2 (fun j x => (Fa[j]!)[x]!) 71

theorem rec_eq : f48Rec Fa 71 = R := by
  unfold f48Rec
  rw [fa_size]

theorem R_parts : R.ord.size = 512 ∧ (∀ i < 512, R.ord[i]! = FK.O i) ∧ R.par.size = 512 ∧
    (∀ i < 512, R.par[i]! = FK.Pa i) ∧ R.lab.size = 512 ∧ (∀ i < 512, R.lab[i]! = FK.La i) ∧
    R.pos.size = 819 ∧ (∀ y < 819, R.pos[y]! = if FK.Ps y < 512 then FK.Ps y else 819) ∧
    OTree (fun j x => (Fa[j]!)[x]!) FK.O FK.Pa FK.La 2 512 :=
  orbBFS_of_K (W := FK.W) (by norm_num) r_parts.1 r_parts.2.1 r_parts.2.2.1 hC hact
    (beqT FK.ch4236Run)

theorem ord_get {i : ℕ} (hi : i < 512) : R.ord[i]! = FK.O i := R_parts.2.1 i hi

theorem par_get {i : ℕ} (hi : i < 512) : R.par[i]! = FK.Pa i := R_parts.2.2.2.1 i hi

theorem lab_get {i : ℕ} (hi : i < 512) : R.lab[i]! = FK.La i := R_parts.2.2.2.2.2.1 i hi

theorem tree {i : ℕ} (h0 : 0 < i) (hi : i < 512) :
    FK.Pa i < i ∧ FK.La i < 2 ∧ (Fa[FK.La i]!)[FK.O (FK.Pa i)]! = FK.O i :=
  R_parts.2.2.2.2.2.2.2.2 i h0 hi

theorem o_inj {i j : ℕ} (hi : i < 512) (hj : j < 512) (e : FK.O i = FK.O j) : i = j := by
  have h := congrArg FK.Ps e
  rwa [(hC.o i hi).2, (hC.o j hj).2] at h

theorem hTR : TRec R 71 where
  lt i hi := by
    rw [ord_get hi]
    exact (hC.o i hi).1
  inj i hi j hj e := by
    rw [ord_get hi, ord_get hj] at e
    exact o_inj hi hj e
  par i h0 hi := by
    rw [par_get hi]
    exact (tree h0 hi).1
  root := by
    rw [ord_get (by norm_num)]
    exact r_parts.1

theorem lay_get {x : ℕ} (hx : x < 819) : lay0[x]! = FK.L0 x := G4235.lay0_get x hx

theorem ps_lt {x : ℕ} (hx : x < 819) (h6 : FK.L0 x = 6) : FK.Ps x < 512 := by
  have h := MatL.allN_iff.1 FK.ch4236L x hx
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  have h2 := h.2
  have e6 : Nat.beq (FK.L0 x) 6 = true := by rw [h6]; rfl
  rw [e6] at h2
  have h3 : Nat.blt (FK.Ps x) 512 = true := h2
  exact G4235.bltT h3

theorem o_ps {x : ℕ} (hx : x < 819) (h : FK.Ps x < 512) : FK.O (FK.Ps x) = x := by
  rcases hC.p x hx with e | ⟨-, e⟩
  · omega
  · exact e

theorem lay_o {i : ℕ} (hi : i < 512) : FK.L0 (FK.O i) = 6 :=
  beqT (MatL.allN_iff.1 FK.ch4236LO i hi)

theorem sg_succ (k f j : ℕ) : FK.sg k (f + 1) j =
    Bool.rec (motive := fun _ => ℕ) (FK.fw (FK.La j) (FK.sg k f (FK.Pa j))) k (Nat.beq j 0) := rfl

theorem aF_eq (k y : ℕ) : FK.aF k y =
    Bool.rec (motive := fun _ => ℕ) y (FK.sg k 512 (FK.Ps y)) (Nat.blt (FK.Ps y) 512) := rfl

theorem sg_eq {k : ℕ} (hk : k < 819) :
    ∀ j < 512, ∀ f, j < f → tSig Fa R k f j = FK.sg k f j ∧ FK.sg k f j < 819 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj f hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [tSig_add]
    by_cases h0 : j = 0
    · subst h0
      rw [if_pos rfl, sg_succ]
      exact ⟨rfl, hk⟩
    · have ht := tree (by omega) hj
      have hs : FK.sg k (f + 1) j = FK.fw (FK.La j) (FK.sg k f (FK.Pa j)) := by
        have e : Nat.beq j 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
        rw [sg_succ, e]
      obtain ⟨e, b⟩ := ih (FK.Pa j) ht.1 (by omega) f (by omega)
      rw [if_neg h0, hs, par_get hj, lab_get hj, e]
      exact hF ht.2.1 b

theorem aF_get {k : ℕ} (hk : k < 819) {y : ℕ} (hy : y < 819) :
    (f48TArr Fa R 71 k)[y]! = FK.aF k y ∧ FK.aF k y < 819 := by
  obtain ⟨-, hv, hf⟩ := tArr_spec (F := Fa) (k := k) hTR (by norm_num)
  by_cases hp : FK.Ps y < 512
  · have ha : FK.aF k y = FK.sg k 512 (FK.Ps y) := by
      have e : Nat.blt (FK.Ps y) 512 = true := by simpa using hp
      rw [aF_eq, e]
    obtain ⟨e, b⟩ := sg_eq hk _ hp 512 hp
    rw [ha, ← e]
    have := hv _ hp
    rw [ord_get hp, o_ps hy hp] at this
    rw [this]
    exact ⟨rfl, by rw [e]; exact b⟩
  · have ha : FK.aF k y = y := by
      have e : Nat.blt (FK.Ps y) 512 = false := Bool.eq_false_iff.2 fun h => hp (G4235.bltT h)
      rw [aF_eq, e]
    rw [ha]
    refine ⟨hf y hy fun i hi e => hp ?_, hy⟩
    rw [ord_get hi] at e
    rw [← e, (hC.o i hi).2]
    exact hi

theorem gIt_eq (k : ℕ) : ∀ c x, FK.gIt k c x = (FK.gF k)^[c] x
  | 0, _ => rfl
  | c + 1, x => by
    rw [Function.iterate_succ_apply', ← gIt_eq k c x]
    rfl

theorem fullFail {M i : ℕ} (hM : M < 2 ^ 40) (hi : i < 512) (h0 : i ≠ 0)
    (hP : FK.pwOK M i = true) :
    f48FullFail M (f48EvalW permArrs f48NWord) (f48EvalW permArrs f48QWord)
      (f48TArr Fa R 71 (FK.O i)) = true := by
  have hk : FK.O i < 819 := (hC.o i hi).1
  set a := f48TArr Fa R 71 (FK.O i)
  set n := f48EvalW permArrs f48NWord
  set q := f48EvalW permArrs f48QWord
  have hm : ∀ y < 819, (compA 819 n a)[y]! = FK.mF (FK.O i) y ∧ FK.mF (FK.O i) y < 819 := by
    intro y hy
    obtain ⟨e1, b1⟩ := aF_get hk hy
    rw [compA_get hy, e1]
    exact hn b1
  have hS := MatL.allN_iff.1 FK.ch4236S i hi
  unfold f48FullFail
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hc : FK.C i = 0
  · left
    have hS' : (FK.X i < 819) ∧ ¬ FK.mF (FK.O i) (FK.mF (FK.O i) (FK.X i)) = FK.X i := by
      simpa [h0, hc] using hS
    rw [Bool.eq_false_iff]
    intro he
    have := allLt_iff.1 he (FK.X i) hS'.1
    rw [compA_get hS'.1, idA_get hS'.1, (hm _ hS'.1).1, (hm _ (hm _ hS'.1).2).1] at this
    exact hS'.2 (beq_iff_eq.1 this)
  · right
    unfold FK.pwOK at hP
    have hP' : (FK.X i < 819 ∧ FK.gIt (FK.O i) (FK.C i) (FK.X i) = FK.X i) ∧
        ¬ FK.gIt (FK.O i) (M % FK.C i) (FK.X i) = FK.X i := by
      simpa [h0, hc] using hP
    obtain ⟨⟨hx, hcyc⟩, hne⟩ := hP'
    have hg : ∀ y < 819, (compA 819 (compA 819 n a) q)[y]! = FK.gF (FK.O i) y ∧
        FK.gF (FK.O i) y < 819 := by
      intro y hy
      obtain ⟨e1, b1⟩ := hq hy
      rw [compA_get hy, e1]
      exact hm _ b1
    rw [Bool.eq_false_iff]
    intro he
    have := allLt_iff.1 he (FK.X i) hx
    rw [powA_get (fun y hy => by rw [(hg y hy).1]; exact (hg y hy).2) hM hx, idA_get hx,
      iter_congr (h := FK.gF (FK.O i)) (fun y hy => (hg y hy).1)
        (fun y hy => by rw [(hg y hy).1]; exact (hg y hy).2) M _ hx] at this
    rw [gIt_eq] at hcyc hne
    rw [iter_mod hcyc] at this
    exact hne (beq_iff_eq.1 this)

theorem lines : f48LinesOK lineTab (f48EvalW permArrs f48NWord) Ba = true := by
  unfold f48LinesOK
  refine allLt_iff.2 fun l hl => ?_
  have h := MatL.allN_iff.1 FK.ch4236Ln l hl
  have e0 : f48LineHas0 lineTab l = FK.has0F l := by
    unfold f48LineHas0 f48LinePt FK.has0F
    rw [G4235.hP, G4235.hP, G4235.hP]
    rfl
  have e1 : ∀ a b c, f48LineIn lineTab l a b c = FK.lineInF l a b c := by
    intro a b c
    unfold f48LineIn f48LinePt FK.lineInF
    rw [G4235.hP, G4235.hP, G4235.hP]
    rfl
  have e2 : ∀ j ∈ List.range 8, f48LineInImg lineTab l (compA 819 Ba[j]! (f48EvalW permArrs f48NWord)) =
      FK.lineInF l (FK.bw j (FK.nw 0)) (FK.bw j (FK.nw 1)) (FK.bw j (FK.nw 5)) := by
    intro j hj
    have hj' := List.mem_range.1 hj
    unfold f48LineInImg
    rw [e1, compA_get (i := 0) (by norm_num), compA_get (i := 1) (by norm_num),
      compA_get (i := 5) (by norm_num),
      (hn (x := 0) (by norm_num)).1, (hn (x := 1) (by norm_num)).1, (hn (x := 5) (by norm_num)).1,
      (hB hj' (hn (x := 0) (by norm_num)).2).1, (hB hj' (hn (x := 1) (by norm_num)).2).1,
      (hB hj' (hn (x := 5) (by norm_num)).2).1]
  rw [e0, e1, H4240.any_congr e2]
  exact h

theorem all2 (p : ℕ → Bool) : allLt 2 p = (p 0 && p 1) := by
  rw [Bool.eq_iff_iff, allLt_iff, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨h 0 (by norm_num), h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ i hi
    interval_cases i
    · exact h0
    · exact h1

theorem fix : f48FixOK Fa = true := by
  unfold f48FixOK
  refine allLt_iff.2 fun x hx => ?_
  have h := MatL.allN_iff.1 FK.ch4236X x hx
  rw [fa_size]
  have e : (allLt 2 fun j => (Fa[j]!)[x]! == x) = (FK.fw 0 x == x && FK.fw 1 x == x) := by
    rw [← (hF (j := 0) (by norm_num) hx).1, ← (hF (j := 1) (by norm_num) hx).1, all2]
  rw [e]
  exact h

theorem orbOK_R : f48OrbOK lay0 Fa R 71 = true := by
  obtain ⟨h1, -, h3, -, h5, -, -, h8, -⟩ := R_parts
  unfold f48OrbOK orbOK
  rw [fa_size]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨h1, h3⟩, h5⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [ord_get (by norm_num)]
    exact r_parts.1
  · refine allLt_iff.2 fun i hi => ?_
    rw [ord_get hi]
    exact decide_eq_true (hC.o i hi).1
  · refine allLt_iff.2 fun i hi => ?_
    by_cases h0 : i = 0
    · simp [h0]
    · obtain ⟨t1, t2, t3⟩ := tree (by omega) hi
      rw [par_get hi, lab_get hi, ord_get hi, ord_get (i := FK.Pa i) (by omega), t3]
      simp [t1, t2]
  · refine allLt_iff.2 fun x hx => ?_
    rw [lay_get hx]
    by_cases h6 : FK.L0 x = 6
    · have hp := ps_lt hx h6
      rw [h8 x hx, if_pos hp, ord_get hp, o_ps hx hp]
      simp [hp]
    · simp [h6]

theorem keyAll {M : ℕ} (hM : M < 2 ^ 40) (hP : ∀ i < 512, FK.pwOK M i = true) :
    f48KeyAll lay0 Fa R M 71 (f48EvalW permArrs f48NWord) (f48EvalW permArrs f48QWord) = true := by
  unfold f48KeyAll
  refine allLt_iff.2 fun k hk => ?_
  rw [lay_get hk]
  by_cases h6 : FK.L0 k = 6
  · have hp := ps_lt hk h6
    have ek := o_ps hk hp
    generalize FK.Ps k = i at hp ek
    subst ek
    unfold f48KeyOK
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    right
    refine ⟨candOK lay0 hTR (by norm_num) fun j hj => ?_, ?_⟩
    · rw [ord_get hj, lay_get (hC.o j hj).1, lay_o hj]
      omega
    · by_cases h0 : i = 0
      · subst h0
        rw [r_parts.1, if_pos (beq_self_eq_true 71)]
        refine tArr_id hTR (by norm_num) fun j h0 hj => ?_
        obtain ⟨t1, -, t3⟩ := tree h0 hj
        rw [lab_get hj, par_get hj, ord_get (lt_trans t1 hj), ord_get hj, t3]
      · have hne : (FK.O i == 71) = false := by
          rw [beq_eq_false_iff_ne, ← r_parts.1]
          exact fun e => h0 (o_inj hp (by norm_num) e)
        rw [if_neg (by rw [hne]; exact Bool.false_ne_true)]
        exact fullFail hM hp h0 (hP i hp)
  · simp [h6]

theorem check {M : ℕ} (hM : M < 2 ^ 40) (hP : ∀ i < 512, FK.pwOK M i = true) :
    hexF48Check M f48Base f48NWord f48QWord f48FWords f48BWords lineTab lay0 permArrs = true := by
  have hN := FK.ch4236N
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at hN
  obtain ⟨hn0, hnm, hqm, hFB, hBB⟩ := hN
  unfold hexF48Check
  simp only [Bool.and_eq_true]
  have e71 : f48Base = 71 := rfl
  rw [e71, rec_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨decide_eq_true hM, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, orbOK_R⟩, keyAll hM hP⟩,
    lines⟩, fix⟩
  · rw [permArrs_size]
    decide +kernel
  · unfold f48NOK
    simp only [Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · unfold eqA
      refine allLt_iff.2 fun x hx => ?_
      rw [compA_get hx, idA_get hx, (hn hx).1, (hn (hn hx).2).1]
      exact beq_iff_eq.2 (beqT (MatL.allN_iff.1 FK.ch4236NN x hx))
    · rw [(hn (x := 0) (by norm_num)).1]
      exact hn0
    · rw [maps_eq fun x hx => (hn hx).1]
      exact hnm
  · rw [maps_eq fun x hx => (hq hx).1]
    exact hqm
  · unfold f48FOK
    rw [fa_size]
    refine allLt_iff.2 fun j hj => ?_
    have h := MatL.allN_iff.1 hFB j hj
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [inB_eq fun x hx => (hF hj hx).1]
      exact h.1
    · have hc : ∀ x < 819, (f48Conj (f48EvalW permArrs f48NWord) Fa[j]!)[x]! =
          FK.nw (FK.fw j (FK.nw x)) := by
        intro x hx
        unfold f48Conj
        rw [compA_get hx, compA_get hx, (hn hx).1, (hF hj (hn hx).2).1, (hn (hF hj (hn hx).2).2).1]
      rw [inB_eq hc]
      exact h.2
  · unfold f48BsOK
    rw [ba_size]
    simp only [Bool.and_eq_true]
    refine ⟨by decide, allLt_iff.2 fun j hj => ?_⟩
    rw [inB_eq fun x hx => (hB hj hx).1]
    exact MatL.allN_iff.1 hBB j hj
  · unfold f48LayOK
    simp only [Bool.and_eq_true]
    refine ⟨?_, allLt_iff.2 fun x hx => ?_⟩
    · rw [lay_get (by norm_num), beqT FK.ch4236L0]
      rfl
    · have h := MatL.allN_iff.1 FK.ch4236L x hx
      simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
      rw [lay_get hx]
      exact h.1

theorem c4236 : CFSG.D4Hex.hexF48Check CFSG.D4Hex.f48Order CFSG.D4Hex.f48Base CFSG.D4Hex.f48NWord
      CFSG.D4Hex.f48QWord CFSG.D4Hex.f48FWords CFSG.D4Hex.f48BWords CFSG.D4Hex.lineTab
      CFSG.D4Hex.lay0 CFSG.D4Hex.permArrs = true ∧
    CFSG.D4Hex.hexF48Check CFSG.D4Hex.f48Order3 CFSG.D4Hex.f48Base CFSG.D4Hex.f48NWord
      CFSG.D4Hex.f48QWord CFSG.D4Hex.f48FWords CFSG.D4Hex.f48BWords CFSG.D4Hex.lineTab
      CFSG.D4Hex.lay0 CFSG.D4Hex.permArrs = true :=
  ⟨check (by decide) (MatL.allN_iff.1 FK.ch4236P), check (by decide) (MatL.allN_iff.1 FK.ch4236P3)⟩

end CertificateChecks.KernelS63.F4236

end

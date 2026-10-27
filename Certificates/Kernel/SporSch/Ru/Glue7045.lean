
module

public import Certificates.Kernel.SporSch.Ru.Cnt7045K
public import Certificates.Kernel.SporSch.Ru.K07045K
public import Certificates.Kernel.SporSch.Ru.Q7307
public import Certificates.Kernel.SporSch.Ru.Iso7047
public import Certificates.Kernel.SporSch.Ru.G2Ru7164
public import Certificates.Kernel.SporSch.Ru.Assemble2259
public import Certificates.Kernel.SporSch.Tits.Graph2265N
public import Certificates.Kernel.Misc.Tits.E07043
public import CFSG.Certificates.Kernel.SporSch.RowTreeSound
public import CFSG.Certificates.Kernel.SporSch.OrbRootsSound
public import CFSG.Certificates.Kernel.SporSch.RuOrbKGS
public import CFSG.Certificates.Kernel.Fi22Rk.Side
public import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Glue7045

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.OrbLab CFSG.KS.RowTree
  CFSG.KS.RuTree CFSG.KLC.Fi22 CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.G2Ru7164 CFSG.Quasithin.RuRank3 CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.KC.BfsPin

@[expose, reducible] noncomputable def pf (p i : Nat) : Nat := pg 12 (mask 12) p i

theorem pinv_left {p : Nat} (hp : P p) {i : Nat} (hi : i < 4060) : pf (pinv p) (pf p i) = i :=
  CFSG.KS.PinvS.pg_pinvS (by norm_num) hp.2 hi

theorem pinv_right {p : Nat} (hp : P p) {j : Nat} (hj : j < 4060) : pf p (pf (pinv p) j) = j := by
  obtain ⟨i, hi, e⟩ := CFSG.KS.PinvS.surj_of_injK hp.2 j hj
  have e' : pf p i = j := e
  rw [← e', pinv_left hp hi]

theorem pinv_lt {p : Nat} (hp : P p) {j : Nat} (hj : j < 4060) : pf (pinv p) j < 4060 :=
  CFSG.KS.PinvS.pinvS_lt (by norm_num) hp.2 j hj

theorem pc_get (a b : Nat) {i : Nat} (hi : i < 4060) : pf (pc a b) i = pf a (pf b i) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hi

theorem pinv_pc {a b : Nat} (ha : P a) (hb : P b) {y : Nat} (hy : y < 4060) :
    pf (pinv (pc a b)) y = pf (pinv b) (pf (pinv a) y) := by
  have hz := pinv_lt hb (pinv_lt ha hy)
  have e : pf (pc a b) (pf (pinv b) (pf (pinv a) y)) = y := by
    rw [pc_get a b hz, pinv_right hb (pinv_lt ha hy), pinv_right ha hy]
  have h := pinv_left (P_pc ha hb) hz
  rw [e] at h
  exact h

theorem pinv_pinv {a : Nat} (ha : P a) {y : Nat} (hy : y < 4060) : pf (pinv (pinv a)) y = pf a y := by
  have h := pinv_left (P_pinv ha) (ha.2.1 y hy)
  rw [pinv_left ha hy] at h
  exact h

theorem pinv_pid {y : Nat} (hy : y < 4060) : pf (pinv pid) y = y := by
  have e : pf pid y = y := CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hy
  have h := pinv_left P_pid hy
  rw [e] at h
  exact h

theorem hPA : ∀ j < 2, P (Q7307.Af j) := fun j hj => by
  interval_cases j
  · exact PP_of_permOK hsz Q7307.kPerm0
  · exact PP_of_permOK hsz Q7307.kPerm1

theorem hSA : ∀ j < 2, ruGensA[j]! = unpack 4060 12 (Q7307.Af j) := fun j hj => by
  interval_cases j
  · rw [show ruGensA[0]! = ruA0A by simp [ruGensA], a0_eq]
    rfl
  · rw [show ruGensA[1]! = ruA1A by simp [ruGensA], a1_eq]
    rfl

theorem hinvA : ruGensInvA = ruGensA.map (invCand 4060) := by
  simp [ruGensInvA, ruGensA, ruInv]

theorem letters {x : Nat} (hx : x < 4060) : ∀ l ∈ Iso7047.twK 32 x, l ≠ 0 ∧ l.natAbs ≤ 2 := by
  have h := allN_spec Iso7047.kTree x hx
  simp only [bAnd_iff] at h
  intro l hl
  rcases Iso7047.good_of h.1 l hl with rfl | rfl | rfl | rfl <;> decide

@[expose] noncomputable def T (x : Nat) : Nat := wK Q7307.Af (Iso7047.twK 32 x)

@[expose] noncomputable def TI (x y : Nat) : Nat := pf (pinv (T x)) y

theorem tree_eq {x : Nat} (hx : x < 4060) : ruTreeArr x = unpack 4060 12 (T x) ∧ P (T x) := by
  have e : ruTreeWord x = Iso7047.twK 32 x := Iso7047.treeWordAux_eq 32 x hx
  change wordA 4060 ruGensA ruGensInvA (ruTreeWord x) = _ ∧ _
  rw [hinvA, e]
  exact wordA_eq (S := ruGensA) (k := 2) (by simp [ruGensA]) hSA hPA _ (letters hx)

theorem ti_eq {x : Nat} (hx : x < 4060) : ruTI x = unpack 4060 12 (pinv (T x)) := by
  change invCand 4060 (ruTreeArr x) = _
  rw [(tree_eq hx).1, inv_eq (tree_eq hx).2]

theorem isInv_tree {x : Nat} (hx : x < 4060) :
    isInvA 4060 (ruTreeArr x) (invCand 4060 (ruTreeArr x)) = true := by
  rw [(tree_eq hx).1]
  exact CFSG.KC.Fi22RkS.isInvA_PP (tree_eq hx).2

theorem twK_zero (f : Nat) : Iso7047.twK f 0 = [] := by
  cases f <;> rfl

theorem twK_succ (f x : Nat) (hx : x ≠ 0) :
    Iso7047.twK (f + 1) x = ruTreeLetter (Ru7045.labK x) :: Iso7047.twK f (Ru7045.parK x) := by
  have hb : Nat.beq x 0 = false := by
    cases h : Nat.beq x 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h) hx
  have e : Iso7047.twK (f + 1) x = Bool.rec (motive := fun _ => List Int)
      (List.cons (ruTreeLetter (pg 4 (mask 4) Iso7047.Lab x))
        (Iso7047.twK f (pg 12 (mask 12) Iso7047.Par x))) [] (Nat.beq x 0) := rfl
  rw [e, hb]
  rfl

theorem twK_reach : ∀ f x, reachK Ru7045.parK f x = true → ∀ g,
    Iso7047.twK (f + g) x = Iso7047.twK f x
  | 0, x, h, g => by
    have hx : x = 0 := Nat.eq_of_beq_eq_true h
    subst hx
    rw [twK_zero, twK_zero]
  | f + 1, x, h, g => by
    rw [reachK_succ] at h
    by_cases hx : x = 0
    · subst hx
      rw [twK_zero, twK_zero]
    · rw [if_neg hx] at h
      rw [show f + 1 + g = (f + g) + 1 by omega, twK_succ _ _ hx, twK_succ _ _ hx,
        twK_reach f _ h g]

theorem rows_all : ∀ c < 16, Ru7045.rows c = true := by
  intro c hc
  interval_cases c
  exacts [Ru7045.ch7045row0, Ru7045.ch7045row1, Ru7045.ch7045row2, Ru7045.ch7045row3,
    Ru7045.ch7045row4, Ru7045.ch7045row5, Ru7045.ch7045row6, Ru7045.ch7045row7,
    Ru7045.ch7045row8, Ru7045.ch7045row9, Ru7045.ch7045row10, Ru7045.ch7045row11,
    Ru7045.ch7045row12, Ru7045.ch7045row13, Ru7045.ch7045row14, Ru7045.ch7045row15]

theorem row_at {x : Nat} (h0 : 0 < x) (hx : x < 4060) : Ru7045.rowAt x = true := by
  have h := rngK_spec (rows_all (x / 256) (by omega)) x
    (by change 256 * (x / 256) ≤ x; omega) (by change x < 256 * (x / 256) + 256; omega)
  rcases orB_iff'.1 h with h | h
  · exact absurd (Nat.eq_of_beq_eq_true h) (Nat.pos_iff_ne_zero.mp h0)
  · rcases orB_iff'.1 h with h | h
    · have hb : Nat.blt x 4060 = true := Nat.blt_eq.mpr hx
      rw [hb] at h
      exact absurd h (by decide)
    · exact h

theorem reach32 {x : Nat} (h0 : 0 < x) (hx : x < 4060) : reachK Ru7045.parK 32 x = true :=
  (andB_iff'.1 (row_at h0 hx)).1

theorem par_lt {x : Nat} (hx : x < 4060) : Ru7045.parK x < 4060 := (Iso7047.range_of hx).2.2.2.2

theorem letter_good (c : Nat) : ruTreeLetter c ≠ 0 ∧ (ruTreeLetter c).natAbs ≤ 2 := by
  unfold ruTreeLetter
  split_ifs <;> decide

theorem P_letK {l : Int} (hl : l ≠ 0 ∧ l.natAbs ≤ 2) : P (letK Q7307.Af l) := by
  unfold letK
  by_cases hpos : 0 < l
  · rw [decide_eq_true hpos]
    exact hPA _ (by omega)
  · rw [decide_eq_false hpos]
    exact P_pinv (hPA _ (by omega))

theorem T_step {x : Nat} (h0 : 0 < x) (hx : x < 4060) :
    T x = pc (letK Q7307.Af (ruTreeLetter (Ru7045.labK x))) (T (Ru7045.parK x)) := by
  have hr := reach32 h0 hx
  rw [show (32 : Nat) = 31 + 1 from rfl, reachK_succ, if_neg (by omega)] at hr
  have e1 : Iso7047.twK 32 (Ru7045.parK x) = Iso7047.twK 31 (Ru7045.parK x) := twK_reach 31 _ hr 1
  unfold T
  rw [e1, show (32 : Nat) = 31 + 1 from rfl, twK_succ 31 x (by omega)]
  rfl

@[expose] noncomputable def Hf (c y : Nat) : Nat := pf (pinv (letK Q7307.Af (ruTreeLetter c))) y

theorem ti_step {x : Nat} (h0 : 0 < x) (hx : x < 4060) {y : Nat} (hy : y < 4060) :
    TI x y = TI (Ru7045.parK x) (Hf (Ru7045.labK x) y) := by
  unfold TI Hf
  rw [T_step h0 hx, pinv_pc (P_letK (letter_good _)) (tree_eq (par_lt hx)).2 hy]

theorem ti_zero {y : Nat} (hy : y < 4060) : TI 0 y = y := by
  unfold TI T
  rw [twK_zero]
  exact pinv_pid hy

theorem net_of {NW A : Nat} (hv : nwValid NW = true) (h : Ru2259.arrK NW A = true) (hA : P A) :
    NetOf NW (fun s => pf A s) := by
  obtain ⟨g, -⟩ := Ru2259.arr_spec hv h
  unfold NetOf
  refine ⟨hv, fun s hs => ?_, fun s hs => hA.2.1 s hs, fun s hs t ht e => hA.2.2 s hs t ht e⟩
  rw [g s hs]
  by_cases hl : s < 4060
  · rw [if_pos hl, if_pos hl, unpack_get' hl]
  · rw [if_neg hl, if_neg hl]

theorem net0 : NetOf RuTD.NW0 (fun s => pf A0 s) := net_of Ru2259.nw0 Ru2259.arr0 (hPA 0 (by norm_num))

theorem net1 : NetOf RuTD.NW1 (fun s => pf A1 s) := net_of Ru2259.nw1 Ru2259.arr1 (hPA 1 (by norm_num))

theorem hH1 : ∀ y < 4060, Hf 1 y < 4060 ∧ pf A0 (Hf 1 y) = y := fun y hy => by
  have e : letK Q7307.Af (ruTreeLetter 1) = A0 := rfl
  unfold Hf
  rw [e]
  exact ⟨pinv_lt (hPA 0 (by norm_num)) hy, pinv_right (hPA 0 (by norm_num)) hy⟩

theorem hH2 : ∀ y < 4060, Hf 2 y < 4060 ∧ pf A1 (Hf 2 y) = y := fun y hy => by
  have e : letK Q7307.Af (ruTreeLetter 2) = A1 := rfl
  unfold Hf
  rw [e]
  exact ⟨pinv_lt (hPA 1 (by norm_num)) hy, pinv_right (hPA 1 (by norm_num)) hy⟩

theorem hH3 : ∀ y < 4060, Hf 3 y = pf A0 y := fun y hy => by
  have e : letK Q7307.Af (ruTreeLetter 3) = pinv A0 := rfl
  unfold Hf
  rw [e]
  exact pinv_pinv (hPA 0 (by norm_num)) hy

theorem hH4 : ∀ c, c ≠ 1 → c ≠ 2 → c ≠ 3 → ∀ y < 4060, Hf c y = pf A1 y := fun c h1 h2 h3 y hy => by
  have e0 : ruTreeLetter c = -2 := by simp [ruTreeLetter, h1, h2, h3]
  have e : letK Q7307.Af (-2) = pinv A1 := rfl
  unfold Hf
  rw [e0, e]
  exact pinv_pinv (hPA 1 (by norm_num)) hy

theorem rows : ∀ x < 4060, Nat.shiftRight (Ru7045.Row x) 4060 = 0 ∧
    ∀ y < 4060, ((Ru7045.Row x).testBit y = true ↔ Q7307.Lf (TI x y) = Q7307.Lf 1) :=
  rows_sound (D := fun y => Q7307.Lf y = Q7307.Lf 1) net0 net1 hH1 hH2 hH3 hH4 Ru7045.kRoot
    (fun _ _ => Iff.rfl) (fun x h0 hx => row_at h0 hx) (fun x hx => par_lt hx)
    (fun y hy => ti_zero hy) (fun x h0 hx y hy => ti_step h0 hx hy)

theorem rowA_eq {v x : Nat} (hv : v < 4060) (hx : x < 4060) :
    ruRowA (ruTI v) x = (Ru7045.Row v).testBit x := by
  have hti : (ruTI v)[x]! = TI v x := by
    rw [ti_eq hv, unpack_get' hx]
    rfl
  have hlt : TI v x < 4060 := pinv_lt (tree_eq hv).2 hx
  unfold ruRowA
  rw [hti, Q7307.qlab_get hlt, Q7307.qlab_get (by norm_num), Bool.eq_iff_iff, beq_iff_eq]
  exact ((rows v hv).2 x hx).symm

theorem inS_eq {x : Nat} (hx : x < 4060) : ruInS x = Ru7045.inS x := by
  unfold ruInS Ru7045.inS
  rw [Q7307.qlab_get hx, show ruG0 = 2808 from rfl, Q7307.qlab_get (by norm_num), Q7307.nat_beq]

theorem popK_eq (r : Nat) : ∀ n, Ru7045.popK r n = (List.range n).countP fun i => r.testBit i
  | 0 => rfl
  | n + 1 => by
    change Bool.rec (motive := fun _ => Nat) (Ru7045.popK r n) (Nat.succ (Ru7045.popK r n))
      (bt r n) = _
    rw [List.range_succ, List.countP_append, popK_eq r n, bt_eq]
    cases h : r.testBit n <;> simp [h]

theorem mS_bit : ∀ n y, (Ru7045.mS n).testBit y = (decide (y < n) && Ru7045.inS y)
  | 0, y => by simp [Ru7045.mS]
  | n + 1, y => by
    change (Bool.rec (motive := fun _ => Nat) (Ru7045.mS n)
      (Nat.lor (Ru7045.mS n) (Nat.shiftLeft 1 n)) (Ru7045.inS n)).testBit y = _
    by_cases hy : y = n
    · subst hy
      cases h : Ru7045.inS y
      · simp [mS_bit y y]
      · rw [show Nat.lor (Ru7045.mS y) (Nat.shiftLeft 1 y) = Ru7045.mS y ||| 1 <<< y from rfl]
        simp [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow_self, h]
    · have e : (decide (y < n + 1) && Ru7045.inS y) = (decide (y < n) && Ru7045.inS y) := by
        by_cases h : y < n
        · simp [h, show y < n + 1 by omega]
        · simp [h, show ¬ y < n + 1 by omega]
      rw [e, ← mS_bit n y]
      cases Ru7045.inS n
      · rfl
      · rw [show Nat.lor (Ru7045.mS n) (Nat.shiftLeft 1 n) = Ru7045.mS n ||| 1 <<< n from rfl,
          Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_false (Ne.symm hy),
          Bool.or_false]

theorem cnt_eq {v : Nat} (hv : v < 4060) :
    ruCnt (ruTI v) = Ru7045.popK (Nat.land (Nat.land (Ru7045.mS 4060) (Ru7045.Row 1)) (Ru7045.Row v))
      4060 := by
  unfold ruCnt
  rw [popK_eq]
  apply List.countP_congr
  intro x hx
  have hx' := List.mem_range.1 hx
  rw [show Nat.land (Nat.land (Ru7045.mS 4060) (Ru7045.Row 1)) (Ru7045.Row v) =
      Ru7045.mS 4060 &&& Ru7045.Row 1 &&& Ru7045.Row v from rfl, Nat.testBit_and, Nat.testBit_and,
    mS_bit, inS_eq hx', show ruTI1 = ruTI 1 from rfl, rowA_eq (by norm_num) hx', rowA_eq hv hx',
    decide_eq_true hx', Bool.true_and]

theorem nbrK_iff (j : Nat) : ∀ k, Ru7045.nbrK k j = true ↔ ∃ i < k, pgW 11 TitsGN.NB i = j
  | 0 => by simp [Ru7045.nbrK]
  | k + 1 => by
    change orB (Ru7045.nbrK k j) (Nat.beq (pgW 11 TitsGN.NB k) j) = true ↔ _
    rw [orB_iff', nbrK_iff j k, Nat.beq_eq]
    constructor
    · rintro (⟨i, hi, e⟩ | e)
      · exact ⟨i, by omega, e⟩
      · exact ⟨k, by omega, e⟩
    · rintro ⟨i, hi, e⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact Or.inl ⟨i, h, e⟩
      · subst h
        exact Or.inr e

theorem nbr0_eq (j : Nat) : (titsNbr[0]!).contains j = Ru7045.nbrK 10 j := by
  rw [TitsGraph.nbr_get (by norm_num), Bool.eq_iff_iff, nbrK_iff, Array.contains_iff_mem,
    Array.mem_ofFn]
  constructor
  · rintro ⟨i, e⟩
    exact ⟨i.val, i.isLt, by simpa using e⟩
  · rintro ⟨i, hi, e⟩
    exact ⟨⟨i, hi⟩, by simpa using e⟩

theorem eqB_eq (a b : Bool) : Ru7045.eqB a b = (a == b) := by
  cases a <;> cases b <;> rfl

theorem count_ok {j : Nat} (hj : j < 1755) : ruCountOK j = true := by
  obtain ⟨dj, djl, -⟩ := Iso7047.d_get hj
  have hc : Ru7045.cnt (j / 110) = true := by
    have key : ∀ c < 16, Ru7045.cnt c = true := by
      intro c hc
      interval_cases c
      exacts [Ru7045.ch7045cnt0, Ru7045.ch7045cnt1, Ru7045.ch7045cnt2, Ru7045.ch7045cnt3,
        Ru7045.ch7045cnt4, Ru7045.ch7045cnt5, Ru7045.ch7045cnt6, Ru7045.ch7045cnt7,
        Ru7045.ch7045cnt8, Ru7045.ch7045cnt9, Ru7045.ch7045cnt10, Ru7045.ch7045cnt11,
        Ru7045.ch7045cnt12, Ru7045.ch7045cnt13, Ru7045.ch7045cnt14, Ru7045.ch7045cnt15]
    exact key _ (by omega)
  unfold Ru7045.cnt at hc
  rw [sB_eq] at hc
  have h := rngK_spec hc j (by change 110 * (j / 110) ≤ j; omega)
    (by change j < 110 * (j / 110) + 110; omega)
  rcases orB_iff'.1 h with h | h
  · have hb : Nat.blt j 1755 = true := Nat.blt_eq.mpr hj
    rw [hb] at h
    exact absurd h (by decide)
  unfold Ru7045.cntAt at h
  rw [eqB_eq] at h
  unfold ruCountOK
  change (isInvA 4060 (ruTreeArr ruDArr[j]!) (invCand 4060 (ruTreeArr ruDArr[j]!)) &&
    ((ruCnt (ruTI ruDArr[j]!) == 512) == (titsNbr[0]!).contains j)) = true
  rw [dj, isInv_tree djl, cnt_eq djl, nbr0_eq, Bool.true_and]
  have e : (Ru7045.popK (Nat.land (Nat.land (Ru7045.mS 4060) (Ru7045.Row 1)) (Ru7045.Row (pf Iso7047.D j)))
      4060 == 512) = Nat.beq (Ru7045.popK (Nat.land (Nat.land (Ru7045.mS 4060) (Ru7045.Row 1))
        (Ru7045.Row (Ru7045.dPt j))) 4060) 512 := Q7307.nat_beq _ _
  rw [e]
  exact h

theorem w_eq : ∀ i < 20, CFSG.Quasithin.RuRank3.ruW[i]! = Ru7045.wIdx i := by decide

theorem wPt_lt {i : Nat} (hi : i < 20) : Ru7045.wIdx i < 1755 := by
  interval_cases i <;> decide

theorem wti_get {i : Nat} (hi : i < 20) : ruWTI[i]! = ruTI (Ru7045.wPt i) := by
  unfold ruWTI
  rw [getElem!_pos _ i (by simp [CFSG.Quasithin.RuRank3.ruW]; omega), Array.getElem_map,
    ← getElem!_pos CFSG.Quasithin.RuRank3.ruW i (by simp [CFSG.Quasithin.RuRank3.ruW]; omega),
    w_eq i hi, (Iso7047.d_get (wPt_lt hi)).1]
  rfl

theorem wPt_lt' {i : Nat} (hi : i < 20) : Ru7045.wPt i < 4060 := (Iso7047.d_get (wPt_lt hi)).2.1

theorem fpK_eq (x : Nat) : ∀ k, k ≤ 20 → fpK Ru7045.Row Ru7045.wPt k x =
    ((List.range k).map fun i => (Ru7045.Row (Ru7045.wPt i)).testBit x).foldl
      (fun acc b => 2 * acc + b.toNat) 0
  | 0, _ => rfl
  | k + 1, hk => by
    change Nat.add (Nat.mul 2 (fpK Ru7045.Row Ru7045.wPt k x))
      (Bool.rec (motive := fun _ => Nat) 0 1 (bt (Ru7045.Row (Ru7045.wPt k)) x)) = _
    rw [List.range_succ, List.map_append, List.foldl_append, ← fpK_eq x k (by omega), bt_eq]
    cases h : (Ru7045.Row (Ru7045.wPt k)).testBit x <;> simp [h, Nat.mul_eq, Nat.add_eq]

theorem fp_eq {x : Nat} (hx : x < 4060) : ruFP x = Ru7045.fp x := by
  unfold ruFP Ru7045.fp
  rw [fpK_eq x 20 le_rfl]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [wti_get hi', rowA_eq (wPt_lt' hi') hx]

theorem fpArr_get {x : Nat} (hx : x < 4060) : ruFPArr[x]! = Ru7045.fp x := by
  unfold ruFPArr
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, fp_eq hx]

theorem fp_ok : (CFSG.Monster.B.Co2.Native.allLt 20 fun i =>
      decide (CFSG.Quasithin.RuRank3.ruW[i]! < 1755) &&
      isInvA 4060 (ruTreeArr ruDArr[CFSG.Quasithin.RuRank3.ruW[i]!]!) ruWTI[i]!) = true ∧
    (CFSG.Monster.B.Co2.Native.allLt 4060 fun x => !(ruInS x) ||
      CFSG.Monster.B.Co2.Native.allLt x fun y =>!(ruInS y) || ruFPArr[x]! != ruFPArr[y]!) = true := by
  refine ⟨CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_, CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_⟩
  · have hw := w_eq i hi
    have e : ruWTI[i]! = invCand 4060 (ruTreeArr ruDArr[CFSG.Quasithin.RuRank3.ruW[i]!]!) := by
      rw [wti_get hi, hw, (Iso7047.d_get (wPt_lt hi)).1]
      rfl
    rw [e, hw, (Iso7047.d_get (wPt_lt hi)).1, isInv_tree (Iso7047.d_get (wPt_lt hi)).2.1,
      Bool.and_true, decide_eq_true (wPt_lt hi)]
  · rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hsx : ruInS x = true
    · refine Or.inr (CFSG.Monster.B.Co2.allLt_iff.2 fun y hy => ?_)
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hsy : ruInS y = true
      · refine Or.inr ?_
        rw [fpArr_get hx, fpArr_get (by omega), bne_iff_ne]
        intro e
        have := fp_inj Ru7045.kKeys Ru7045.kCover hx (by omega) (by rwa [← inS_eq hx])
          (by rwa [← inS_eq (by omega)]) e
        omega
      · exact Or.inl (by simpa using hsy)
    · exact Or.inl (by simpa using hsx)

theorem gs : titsK0Gens.size = 3 := by simp [titsK0Gens]

theorem roots_eq : (orbLabels 1755 titsK0Gens).2.size = KernelMisc.E7043.Mv ∧
    ∀ c < KernelMisc.E7043.Mv, (orbLabels 1755 titsK0Gens).2[c]! = KernelMisc.E7043.Rf c :=
  orbRoots_of_K gs (fun k hk x hx => KernelMisc.E7043.g_get hk hx) KernelMisc.E7043.kOrb

theorem qr : KernelMisc.E7043.Mv ≤ 1755 ∧ ∀ t < KernelMisc.E7043.Mv,
    K07045.Qf t = KernelMisc.E7043.Rf t := by
  obtain ⟨h1, h2⟩ := andB_iff'.1 K07045.kQR
  exact ⟨Nat.ble_eq.mp h1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec h2 t ht)⟩

theorem orb_ok : orbCheck 1755 titsK0Gens = true := by
  unfold orbCheck
  obtain ⟨r1, r2⟩ := roots_eq
  exact orbitPartOK_forestKG (by norm_num) gs (fun k hk x hx => KernelMisc.E7043.g_get hk hx)
    ⟨r1, fun t ht => by rw [r2 t ht, qr.2 t ht]⟩ qr.1 (fun x hx => KernelMisc.E7043.lab_get hx)
    (fun t ht => allN_spec K07045.kF t ht) (fun e he => allN_spec K07045.kE e (by omega))
    (fun x hx => allN_spec K07045.kP x hx) (fun k hk => allN_spec K07045.kRt k hk)

theorem labCount_eq (c : Nat) : ∀ n, n ≤ 1755 →
    labCount n titsK0Lab c = K07045.cntL n c
  | 0, _ => rfl
  | n + 1, hn => by
    have e1 : labCount (n + 1) titsK0Lab c =
        labCount n titsK0Lab c + if (titsK0Lab[n]! == c) = true then 1 else 0 := by
      simp [labCount, List.range_succ, List.countP_append]
    change _ = Bool.rec (motive := fun _ => Nat) (K07045.cntL n c) (Nat.succ (K07045.cntL n c))
      (Nat.beq (KernelMisc.E7043.Lf n) c)
    rw [e1, labCount_eq c n (by omega), KernelMisc.E7043.lab_get (by omega), Q7307.nat_beq]
    cases h : Nat.beq (KernelMisc.E7043.Lf n) c <;> simp

theorem k0_ok : orbCheck 1755 titsK0Gens = true ∧ labCount 1755 titsK0Lab titsK0Lab[0]! = 975 ∧
    (CFSG.Monster.B.Co2.Native.allLt 1755 fun j => titsK0Lab[j]! == titsK0Lab[0]! ||
      decide (labCount 1755 titsK0Lab titsK0Lab[j]! < 975)) = true ∧
    (CFSG.Monster.B.Co2.Native.allLt 1755 fun j =>
      (titsK0Lab[j]! != titsK0Lab[0]!) == ruRowA ruTIG0 ruDArr[j]!) = true := by
  have l0 := KernelMisc.E7043.lab_get (x := 0) (by norm_num)
  refine ⟨orb_ok, ?_, CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_,
    CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => ?_⟩
  · rw [labCount_eq _ 1755 le_rfl, l0]
    exact Nat.eq_of_beq_eq_true K07045.kC0
  · rw [KernelMisc.E7043.lab_get hj, l0, labCount_eq _ 1755 le_rfl]
    have hs := allN_spec K07045.kSmall _ (Nat.blt_eq.mp (allN_spec K07045.kLt j hj))
    rw [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    rcases orB_iff'.1 hs with h | h
    · exact Or.inl (Nat.eq_of_beq_eq_true h)
    · exact Or.inr (Nat.blt_eq.mp h)
  · obtain ⟨dj, djl, -⟩ := Iso7047.d_get hj
    have hg := allN_spec K07045.kG0 j hj
    rw [show K07045.eqB = Ru7045.eqB from rfl, eqB_eq, bt_eq] at hg
    rw [KernelMisc.E7043.lab_get hj, l0, dj, show ruTIG0 = ruTI 2808 from rfl,
      rowA_eq (by norm_num) djl, bne, Q7307.nat_beq]
    exact hg

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
theorem c7045 :
    ((CFSG.Monster.B.Co2.Native.allLt 1755 fun j => ruCountOK j) = true)
    ∧ ((CFSG.Monster.B.Co2.Native.allLt 20 fun i => decide (CFSG.Quasithin.RuRank3.ruW[i]! < 1755) &&
         isInvA 4060 (ruTreeArr ruDArr[CFSG.Quasithin.RuRank3.ruW[i]!]!) ruWTI[i]!) = true ∧
       (CFSG.Monster.B.Co2.Native.allLt 4060 fun x => !(ruInS x) ||
         CFSG.Monster.B.Co2.Native.allLt x fun y => !(ruInS y) || ruFPArr[x]! != ruFPArr[y]!) = true)
    ∧ (orbCheck 1755 titsK0Gens = true ∧ labCount 1755 titsK0Lab titsK0Lab[0]! = 975 ∧
       (CFSG.Monster.B.Co2.Native.allLt 1755 fun j => titsK0Lab[j]! == titsK0Lab[0]! ||
         decide (labCount 1755 titsK0Lab titsK0Lab[j]! < 975)) = true ∧
       (CFSG.Monster.B.Co2.Native.allLt 1755 fun j => (titsK0Lab[j]! != titsK0Lab[0]!) == ruRowA ruTIG0 ruDArr[j]!) = true) :=
  ⟨CFSG.Monster.B.Co2.allLt_iff.2 fun j hj => count_ok hj, fp_ok, k0_ok⟩

end CertificateChecks.KernelSporSch.Glue7045

end

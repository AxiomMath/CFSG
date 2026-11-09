module

public import Certificates.Kernel.Fi23M.Data
public import Certificates.Data.CFSGNative.Fi23.Data
public import CFSG.Certificates.Kernel.Spor.F3LaneSepSound
public import CFSG.Certificates.Kernel.Spor.F3R

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.KS.F3L CFSG.KS.F3R CFSG.KD.Fi23M CFSG.Sporadic.Fi23.Native

@[expose] noncomputable def lane (X : Nat) : V := ⟨Nat.land X LO, Nat.shiftRight X 64009⟩

@[expose] noncomputable def LsS : List V :=
  [lane (RS 1), lane (RS 3), lane (RS 4), lane (RS 5), lane (RS 6), lane (RS 7)]

@[expose] noncomputable def LI : V := lane ONE

@[expose] noncomputable def WL : V := combL 253 (spreadE 253 253) LI LsS sepTerms

@[expose] noncomputable def sprR (d S M r : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.mul S (Nat.land r (mk (Nat.sub d 1)))) M)
    (Nat.shiftLeft (Nat.shiftRight r (Nat.sub d 1)) (Nat.mul d (Nat.sub d 1)))

@[expose] noncomputable def trRStep (d S M : Nat) (L : V) (j : Nat) (acc : V) : V :=
  strictT acc.p fun ap => strictT acc.m fun am =>
    ⟨Nat.lor ap (Nat.shiftLeft (sprR d S M (blk d L j).p) j),
      Nat.lor am (Nat.shiftLeft (sprR d S M (blk d L j).m) j)⟩

@[expose] noncomputable def trLaneR (d : Nat) (L : V) : V :=
  strictT (spreadE (Nat.sub d 1) d) fun S => strictT (spreadE d d) fun M =>
    Nat.rec (motive := fun _ => V) ⟨nat_lit 0, nat_lit 0⟩ (fun j acc => trRStep d S M L j acc) d

theorem sprR_testBit {e : Nat} (he : 1 ≤ e) {r : Nat} (hr : r < 2 ^ (e + 1)) (a c : Nat)
    (hc : c < e + 1) :
    (sprR (e + 1) (spreadE e (e + 1)) (spreadE (e + 1) (e + 1)) r).testBit ((e + 1) * a + c) =
      (decide (c = 0) && r.testBit a) := by
  have hS : ∀ i, (spreadE e (e + 1)).testBit i = true → e ∣ i := fun i h => by
    rw [spreadE_testBit he] at h
    simp only [decide_eq_true_eq] at h
    exact h.1
  have hy : (r &&& mk e) < 2 ^ e := by
    rw [mk_eq]
    exact Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos)
  have hrb : ∀ k, e + 1 ≤ k → r.testBit k = false := fun k hk =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hk))
  change ((spreadE e (e + 1) * (r &&& mk (e + 1 - 1)) &&& spreadE (e + 1) (e + 1)) |||
    (r >>> (e + 1 - 1)) <<< ((e + 1) * (e + 1 - 1))).testBit ((e + 1) * a + c) = _
  simp only [Nat.add_sub_cancel]
  rw [Nat.testBit_or, Nat.testBit_and, spreadE_testBit (by omega), Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · simp only [Nat.add_zero, dvd_mul_right, true_and, Nat.mul_div_cancel_left _ (by omega : 0 < e + 1),
      decide_true, Bool.true_and]
    rcases lt_trichotomy a e with h | h | h
    · have h1 : ¬ (e + 1) * e ≤ (e + 1) * a := fun h' =>
        absurd (Nat.le_of_mul_le_mul_left h' (by omega)) (by omega)
      have e1 : (e + 1) * a = e * a + a := by ring
      have h' : a < e + 1 := by omega
      have hA : (spreadE e (e + 1) * (r &&& mk e)).testBit ((e + 1) * a) = r.testBit a := by
        rw [e1, testBit_spread he hy a h a _ hS, spreadE_testBit he, Nat.testBit_and, mk_eq,
          Nat.testBit_two_pow_sub_one]
        simp [h, h', Nat.mul_div_cancel_left _ he]
      have h4 : a ≤ e := h.le
      simp [hA, h1, h4]
    · rw [h]
      have e1 : (e + 1) * e = e * (e + 1) + 0 := by ring
      have hB : (spreadE e (e + 1) * (r &&& mk e)).testBit ((e + 1) * e) = false := by
        rw [e1, testBit_spread he hy 0 (by omega) (e + 1) _ hS, spreadE_testBit he]
        simp [Nat.mul_div_cancel_left _ he]
      simp [hB]
    · have h1 : (e + 1) * e ≤ (e + 1) * a := Nat.mul_le_mul_left _ (by omega)
      have h2 : e + 1 ≤ e + ((e + 1) * a - (e + 1) * e) := by
        have : (e + 1) * (e + 1) ≤ (e + 1) * a := Nat.mul_le_mul_left _ (by omega)
        have : (e + 1) * (e + 1) = (e + 1) * e + (e + 1) := by ring
        omega
      have h3 : ¬ a < e + 1 := by omega
      simp [h1, hrb _ h2, hrb a (by omega), h3]
  · have hnd : ¬ (e + 1) ∣ (e + 1) * a + c := fun h =>
      absurd (Nat.le_of_dvd hc0 ((Nat.dvd_add_right (dvd_mul_right _ _)).1 h)) (by omega)
    have hc1 : c ≠ 0 := by omega
    simp only [hnd, false_and, decide_false, Bool.and_false, Bool.false_or, hc1, Bool.false_and]
    by_cases h : (e + 1) * e ≤ (e + 1) * a + c
    · have h2 : e + 1 ≤ e + ((e + 1) * a + c - (e + 1) * e) := by
        by_cases ha : e ≤ a
        · have : (e + 1) * e ≤ (e + 1) * a := Nat.mul_le_mul_left _ ha
          omega
        · have : (e + 1) * a + (e + 1) ≤ (e + 1) * e := by
            have := Nat.mul_le_mul_left (e + 1) (by omega : a + 1 ≤ e)
            rw [Nat.mul_add, Nat.mul_one] at this
            exact this
          omega
      simp [h, hrb _ h2]
    · simp [h]

theorem rowR_testBit {e : Nat} (he : 1 ≤ e) {r : Nat} (hr : r < 2 ^ (e + 1)) (j a b : Nat)
    (hj : j < e + 1) (hb : b < e + 1) :
    (Nat.shiftLeft (sprR (e + 1) (spreadE e (e + 1)) (spreadE (e + 1) (e + 1)) r) j).testBit
      ((e + 1) * a + b) = (decide (b = j) && r.testBit a) := by
  change ((sprR _ _ _ r) <<< j).testBit _ = _
  rw [Nat.testBit_shiftLeft]
  by_cases hjb : j ≤ b
  · have e1 : (e + 1) * a + b - j = (e + 1) * a + (b - j) := by omega
    have h2 : j ≤ (e + 1) * a + b := by omega
    rw [e1, sprR_testBit he hr a (b - j) (by omega)]
    by_cases hbj : b = j
    · simp [hbj]
    · have h3 : b - j ≠ 0 := by omega
      simp [h2, hbj, h3]
  · have hbj : b ≠ j := by omega
    rcases a with _ | a
    · simp [hjb, hbj]
    · have e1 : (e + 1) * (a + 1) + b - j = (e + 1) * a + (e + 1 + b - j) := by
        rw [Nat.mul_succ]
        omega
      have h3 : e + 1 + b - j ≠ 0 := by omega
      rw [e1, sprR_testBit he hr a _ (by omega)]
      simp [hbj, h3]

theorem trRStep_eq (d S M : Nat) (L : V) (j : Nat) (acc : V) :
    trRStep d S M L j acc = ⟨Nat.lor acc.p (Nat.shiftLeft (sprR d S M (blk d L j).p) j),
      Nat.lor acc.m (Nat.shiftLeft (sprR d S M (blk d L j).m) j)⟩ := by
  unfold trRStep
  rw [strictT_eq, strictT_eq]

theorem trRec_testBit {e : Nat} (he : 1 ≤ e) (L : V) : ∀ n, n ≤ e + 1 → ∀ a b, b < e + 1 →
    (Nat.rec (motive := fun _ => V) ⟨0, 0⟩ (fun j acc => trRStep (e + 1) (spreadE e (e + 1))
      (spreadE (e + 1) (e + 1)) L j acc) n : V).p.testBit ((e + 1) * a + b) =
        (decide (b < n) && (decide (a < e + 1) && L.p.testBit ((e + 1) * b + a))) ∧
    (Nat.rec (motive := fun _ => V) ⟨0, 0⟩ (fun j acc => trRStep (e + 1) (spreadE e (e + 1))
      (spreadE (e + 1) (e + 1)) L j acc) n : V).m.testBit ((e + 1) * a + b) =
        (decide (b < n) && (decide (a < e + 1) && L.m.testBit ((e + 1) * b + a))) := by
  intro n
  induction n with
  | zero => intro _ a b _; simp
  | succ n ih =>
    intro hn a b hb
    change (trRStep _ _ _ L n _).p.testBit _ = _ ∧ (trRStep _ _ _ L n _).m.testBit _ = _
    rw [trRStep_eq]
    change (Nat.lor _ _).testBit _ = _ ∧ (Nat.lor _ _).testBit _ = _
    have hor : ∀ x y : Nat, (Nat.lor x y).testBit ((e + 1) * a + b) =
        (x.testBit ((e + 1) * a + b) || y.testBit ((e + 1) * a + b)) :=
      fun x y => Nat.testBit_or x y _
    rw [hor, hor, (ih (by omega) a b hb).1, (ih (by omega) a b hb).2,
      rowR_testBit he (blk_p_lt _ L n) n a b (by omega) hb,
      rowR_testBit he (blk_m_lt _ L n) n a b (by omega) hb, blk_p, blk_m]
    by_cases h : b < n
    · have h2 : b ≠ n := by omega
      have h3 : b < n + 1 := by omega
      simp [h, h2, h3]
    · by_cases h2 : b = n
      · subst h2
        simp
      · have h3 : ¬ b < n + 1 := by omega
        simp [h, h2, h3]

theorem trLaneR_eq {d : Nat} (hd : 2 ≤ d) (L : V) : trLaneR d L = trLane d L := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have he : 1 ≤ e := by omega
  have h1 : Nat.sub (e + 1) 1 = e := by
    change e + 1 - 1 = e
    omega
  unfold trLaneR
  rw [strictT_eq, strictT_eq, h1]
  have hmod : ∀ i, i % (e + 1) < e + 1 := fun i => Nat.mod_lt _ (by omega)
  have hdiv : ∀ i, i / (e + 1) < e + 1 ↔ i < (e + 1) * (e + 1) := fun i =>
    Nat.div_lt_iff_lt_mul (by omega)
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro i
  · have h := (trRec_testBit he L (e + 1) le_rfl (i / (e + 1)) (i % (e + 1)) (hmod i)).1
    rw [Nat.div_add_mod] at h
    rw [h, trLane_p]
    by_cases hi : i < (e + 1) * (e + 1) <;> simp [hmod i, hi, hdiv i]
  · have h := (trRec_testBit he L (e + 1) le_rfl (i / (e + 1)) (i % (e + 1)) (hmod i)).2
    rw [Nat.div_add_mod] at h
    rw [h, trLane_m]
    by_cases hi : i < (e + 1) * (e + 1) <;> simp [hmod i, hi, hdiv i]

@[expose] noncomputable def stepR (r : V) (j : Nat) (acc y : V) : V :=
  Bool.rec (motive := fun _ => V)
    (Bool.rec (motive := fun _ => V) acc (acc.sub y) (Nat.testBit r.m j)) (acc.add y) (Nat.testBit r.p j)

@[expose] noncomputable def combRn (rows : List V) (r : V) (n : Nat) : V × List V :=
  Nat.rec (motive := fun _ => V × List V) (V.zero, rows)
    (fun j st => strictT (stepR r j st.1 (st.2.headD V.zero)).p fun ap =>
      strictT (stepR r j st.1 (st.2.headD V.zero)).m fun am => (⟨ap, am⟩, st.2.tail)) n

@[expose] noncomputable def combR (d : Nat) (rows : List V) (r : V) : V := (combRn rows r d).1

@[expose] noncomputable def rowsT (d : Nat) (L : V) : List V := (List.range d).map (blk d (trLaneR d L))

@[expose] noncomputable def spinR (d : Nat) (Rs : List (List V)) (v : V) (tree : List (Nat × Nat)) :
    Array V :=
  tree.foldl (fun S t => S.push (combR d (Rs.getD t.2 []) S[t.1]!)) #[v]

theorem combRn_eq (d : Nat) (Y : Array V) (rows : List V)
    (hY : ∀ j < d, Y[j]! = (rows.drop j).headD V.zero) (r : V) : ∀ n ≤ d,
    combRn rows r n = (Nat.fold n (fun j _ acc => combStep Y r j acc) V.zero, rows.drop n) := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.fold_zero, List.drop_zero]
    rfl
  | succ n ih =>
    intro hn
    have e : combRn rows r (n + 1) =
        strictT (stepR r n (combRn rows r n).1 ((combRn rows r n).2.headD V.zero)).p fun ap =>
          strictT (stepR r n (combRn rows r n).1 ((combRn rows r n).2.headD V.zero)).m fun am =>
            ((⟨ap, am⟩ : V), (combRn rows r n).2.tail) := rfl
    rw [e, strictT_eq, strictT_eq, ih (by omega), Nat.fold_succ, List.tail_drop]
    have hy := hY n (by omega)
    unfold combStep
    rw [hy]
    unfold stepR
    cases r.p.testBit n <;> cases r.m.testBit n <;> rfl

theorem mulVec_rowsT {d : Nat} (hd : 2 ≤ d) {L : V} (hL : L.wf = true) (u : V) :
    mulVecM d (unlane d L) u = combR d (rowsT d L) u := by
  unfold mulVecM combR rowsT
  rw [transpose_unlane hL, comb_eq_fold, trLaneR_eq hd]
  refine (congrArg Prod.fst (combRn_eq d _ _ (fun j hj => ?_) u d le_rfl)).symm
  rw [unlane_get _ hj, List.drop_eq_getElem_cons (by simp; omega), List.headD_cons,
    List.getElem_map, List.getElem_range]

theorem spinVecs_rowsT {d : Nat} (hd : 2 ≤ d) {Ls : List V} (hLs : ∀ L ∈ Ls, L.wf = true) (v : V)
    (tree : List (Nat × Nat)) (ht : ∀ t ∈ tree, t.2 < Ls.length) :
    spinVecs d (Ls.map (unlane d)).toArray v tree = spinR d (Ls.map (rowsT d)) v tree := by
  unfold spinVecs spinR
  generalize (#[v] : Array V) = S
  induction tree generalizing S with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hlt := ht t List.mem_cons_self
    have hL := hLs _ (List.getElem_mem hlt)
    rw [mats_get hlt, List.getD_eq_getElem _ _ hlt, mulVec_rowsT hd hL]
    have hget : (Ls.map (rowsT d)).getD t.2 [] = rowsT d Ls[t.2] := by
      rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map]
    rw [hget]
    exact ih (fun s hs => ht s (List.mem_cons_of_mem t hs)) _

@[expose] noncomputable def rowsLane (d : Nat) (X : Array V) : V :=
  X.toList.foldr (fun r acc => strictT acc.p fun ap => strictT acc.m fun am =>
    ⟨Nat.lor r.p (Nat.shiftLeft ap d), Nat.lor r.m (Nat.shiftLeft am d)⟩) ⟨nat_lit 0, nat_lit 0⟩

@[expose] noncomputable def beqVL (xs : List V) : List V → Bool :=
  List.rec (motive := fun _ => List V → Bool) (fun ys => ys.isEmpty)
    (fun x _ ih ys => List.rec (motive := fun _ => Bool) false (fun y ys' _ => x.beq y && ih ys') ys) xs

theorem eq_of_beqVL : ∀ xs ys : List V, beqVL xs ys = true → xs = ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => exact (Bool.false_ne_true h).elim
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => exact (Bool.false_ne_true h).elim
    | cons y ys =>
      have e : beqVL (x :: xs) (y :: ys) = (x.beq y && beqVL xs ys) := rfl
      rw [e, Bool.and_eq_true] at h
      rw [V.ext' (V.beq_iff.1 h.1).1 (V.beq_iff.1 h.1).2, ih ys h.2]

@[expose] noncomputable def rowsLaneOK (d : Nat) (X : Array V) : Bool :=
  beqVL X.toList ((List.range d).map (blk d (rowsLane d X)))

theorem eq_unlane_rowsLane {d : Nat} {X : Array V} (h : rowsLaneOK d X = true) :
    X = unlane d (rowsLane d X) := by
  have hl := eq_of_beqVL _ _ h
  have hs : X.size = d := by rw [← Array.length_toList, hl, List.length_map, List.length_range]
  apply Array.ext (by rw [hs, unlane_size])
  intro i h1 h2
  have hi : i < d := by rwa [unlane_size] at h2
  rw [← getElem!_pos (unlane d _) i h2, unlane_get _ hi, ← Array.getElem_toList,
    List.getElem_of_eq hl, List.getElem_map, List.getElem_range]

set_option Elab.async false

theorem sepP_pk : rowsLaneOK 253 (sepP ()) = true := by decide +kernel

theorem sepT_pk : rowsLaneOK 253 (sepTinv ()) = true := by decide +kernel

theorem sepSpin_ok : (rowsLaneOK 253 (spinR 253 (LsS.map (rowsT 253)) (sepVec ()) sepTree) &&
    (mulLane 253 (spreadE 253 253) (rowsLane 253 (sepTinv ()))
      (rowsLane 253 (spinR 253 (LsS.map (rowsT 253)) (sepVec ()) sepTree))).beq LI) = true := by
  decide +kernel

theorem spin_pk : rowsLaneOK 253 (spinR 253 (LsS.map (rowsT 253)) (sepVec ()) sepTree) = true := by
  have h := sepSpin_ok
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem sepPw_ok : eqMK 253 (unlane 253 (mulLane 253 (spreadE 253 253) (rowsLane 253 (sepP ())) WL))
    (projM 253 (sepVec ()) (sepK ())) = true := by decide +kernel

theorem sepTS_ok : (mulLane 253 (spreadE 253 253) (rowsLane 253 (sepTinv ()))
    (rowsLane 253 (spinR 253 (LsS.map (rowsT 253)) (sepVec ()) sepTree))).beq LI = true := by
  have h := sepSpin_ok
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem LI_wf : LI.wf = true := by decide +kernel

theorem id_ok : eqMK 253 (idM 253) (unlane 253 LI) = true := by decide +kernel

theorem idM_eq : idM 253 = unlane 253 LI := by
  have h : eqM 253 (idM 253) (unlane 253 LI) = true := by rw [eqM_eq]; exact id_ok
  exact eq_of_canonM (canonM_idM 253) (canonM_unlane 253 LI_wf) (toMat_eq_of_eqM h)

theorem LsS_wf' : LsS.all V.wf = true := by decide +kernel

theorem LsS_wf : ∀ L ∈ LsS, L.wf = true := by
  intro L hL
  exact List.all_eq_true.1 LsS_wf' L hL

theorem wl_wf : WL.wf = true := by decide +kernel

theorem vec_lt : (sepVec ()).p < 2 ^ 253 ∧ (sepVec ()).m < 2 ^ 253 := by decide

theorem sepK_ok : sepOK 253 (LsS.map (unlane 253)).toArray sepTerms (sepVec ()) (sepK ())
    (sepP ()) (sepTinv ()) sepTree = true := by
  have hd : 0 < 253 := by norm_num
  unfold sepOK
  rw [combM_unlane hd idM_eq LsS sepTerms (by decide), spinVecs_rowsT (by norm_num) LsS_wf
    (sepVec ()) sepTree (by decide)]
  change (_ && (mulVecM 253 (unlane 253 WL) (sepVec ())).isZero && _ && _ && _ && _ && _) = true
  rw [mulVec_unlane hd wl_wf vec_lt.1 vec_lt.2]
  have hT : trLane 253 = trLaneR 253 := funext fun L => (trLaneR_eq (by norm_num) L).symm
  rw [hT]
  have hPw : eqM 253 (mul 253 (sepP ()) (unlane 253 WL)) (projM 253 (sepVec ()) (sepK ())) = true := by
    rw [(congrArg (mul 253 · (unlane 253 WL)) (eq_unlane_rowsLane sepP_pk)).trans (mul_unlane hd _ _),
      eqM_eq]
    exact sepPw_ok
  unfold WL at hPw
  have hS := eq_unlane_rowsLane spin_pk
  have hTS : eqM 253 (mul 253 (sepTinv ()) (spinR 253 (LsS.map (rowsT 253)) (sepVec ()) sepTree))
      (idM 253) = true := by
    rw [(congr (congrArg (mul 253) (eq_unlane_rowsLane sepT_pk)) hS).trans (mul_unlane hd _ _),
      V.ext' (V.beq_iff.1 sepTS_ok).1 (V.beq_iff.1 sepTS_ok).2, idM_eq]
    exact eqM_self (unlane_size 253 LI)
  have hSs : (spinR 253 (LsS.map (rowsT 253)) (sepVec ()) sepTree).size = 253 := by
    rw [hS, unlane_size]
  simp only [hPw, hTS, hSs, beq_self_eq_true, Bool.and_true]
  simp only [wfM_eq, ← Array.all_toList]
  decide +kernel

end CertificateChecks.KernelFi23M

end

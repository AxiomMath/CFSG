module

public import Certificates.Kernel.J4Pent.Canon
public import Certificates.Kernel.J4Pent.Walk
public import Certificates.Kernel.J4Pent.ETest
public import Certificates.Kernel.J4Pent.Misc
public import Certificates.Kernel.J4Pent.Bnd
public import Certificates.Kernel.J4Q.Dec2K
public import CFSG.Certificates.Kernel.J4PentSound

public section

set_option maxRecDepth 4000

namespace CertificateChecks.KernelJ4Pent

open CFSG.KC.J4Pent CFSG.KD.J4Pent CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CertificateChecks.KernelJ4Q CFSG.Sporadic.J4.QT2

theorem rm_eq : rm = 2 ^ 112 - 1 := by decide

theorem nsub (a b : Nat) : Nat.sub a b = a - b := rfl

theorem ONES_eq : ONES = 2 ^ NL - 1 := by
  unfold ONES
  rw [nshl, Nat.one_shiftLeft, nsub]

theorem ones4_eq : Nat.sub (Nat.shiftLeft 1 (Nat.mul 4 NL)) 1 = 2 ^ (4 * NL) - 1 := by
  rw [nshl, Nat.one_shiftLeft, nmul, nsub]

theorem ones_bit {l : Nat} (hl : l < NL) : ONES.testBit l = true := by
  rw [ONES_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hl

theorem wf_parts : (R.length = 112 ∧ ∀ x ∈ R, x < 2 ^ NL) ∧
    (∀ Y ∈ Z, Y.length = 112 ∧ ∀ x ∈ Y, x < 2 ^ NL) ∧ Z.length = 4 ∧
    (∀ s ∈ WS, Disj s) := by
  have h := wf_ok
  simp only [bAnd_eq, Bool.and_eq_true, allB_eq, List.all_eq_true, lenK_eq, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  rw [allLt_iff, nshl, Nat.one_shiftLeft] at h1
  refine ⟨h1, fun Y hY => ?_, h3, fun s hs => ?_⟩
  · have := h2 Y hY
    rwa [allLt_iff, nshl, Nat.one_shiftLeft] at this
  · have := h4 s hs
    unfold stepWf at this
    simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, nland] at this
    exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩

theorem isTr_enc {X : Array V2} (hX : WfA X) :
    IsTr (trJ t0 t1 t2 t3 t4 t5 t6 (encR X)) (encR X) := by
  rw [← enc_transposeRows hK hX]
  intro i hi j hj
  have hT := wf_transposeRows X
  have wX : ∀ i (h : i < X.size), X[i].wf = true := Array.all_eq_true.mp hX.2
  have wT : ∀ i (h : i < (transposeRows X).size), (transposeRows X)[i].wf = true :=
    Array.all_eq_true.mp hT.2
  rw [rowJ_eq wT hj, rowJ_eq wX hi, ← testBit_v2N _ (by omega), ← testBit_v2N _ (by omega)]
  have e := congrFun (congrFun (CFSG.Sporadic.J4.rowsMatrix_transposeRows X) ⟨j, hj⟩) ⟨i, hi⟩
  rw [Matrix.transpose_apply, CFSG.Sporadic.J4.rowsMatrix_apply,
    CFSG.Sporadic.J4.rowsMatrix_apply, CFSG.Sporadic.J4.Native.V2.toVec_apply,
    CFSG.Sporadic.J4.Native.V2.toVec_apply] at e
  revert e
  cases (X[i]?.getD V2.zero).testBit j <;> cases ((transposeRows X)[j]?.getD V2.zero).testBit i <;>
    simp

theorem msf_enc {t : Nat} (ht : t < 6720) :
    WfA (x0Orb.mats[t]!) ∧ encR (x0Orb.mats[t]!) = CFSG.KD.X0O.MSF t :=
  mats_get x0Orb_ok.2.1 x0Orb_ok.2.2 ht

theorem isTr_msf {t : Nat} (ht : t < 6720) :
    IsTr (trJ t0 t1 t2 t3 t4 t5 t6 (CFSG.KD.X0O.MSF t)) (CFSG.KD.X0O.MSF t) := by
  rw [← (msf_enc ht).2]
  exact isTr_enc (msf_enc ht).1

theorem isTr_get {L : List Nat} {k : Nat} {X : Array V2} (hX : WfA X ∧ encR X = getN one L k) :
    IsTr (trJ t0 t1 t2 t3 t4 t5 t6 (getN one L k)) (getN one L k) := by
  rw [← hX.2]
  exact isTr_enc hX.1

theorem isTr_Ai : IsTr (trJ t0 t1 t2 t3 t4 t5 t6 Ai) Ai := isTr_get (base_invs 0)
theorem isTr_Bi : IsTr (trJ t0 t1 t2 t3 t4 t5 t6 Bi) Bi := isTr_get (base_invs 1)
theorem isTr_B : IsTr (trJ t0 t1 t2 t3 t4 t5 t6 B) B := isTr_get (base_gens 1)
theorem isTr_F : IsTr (trJ t0 t1 t2 t3 t4 t5 t6 (getN one XG 0)) (getN one XG 0) :=
  isTr_get (x0Gen_enc (by omega))

theorem laneV_drop96 (l : Nat) : laneV RT l = laneV R l >>> 96 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_laneV, RT, dropK_eq, getD_drop, Nat.testBit_shiftRight, testBit_laneV]

theorem vecJ_lt (x m : Nat) : vecJ (2 ^ 112 - 1) x m < 2 ^ 112 := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  exact testBit_vecJ_ge x m hj

theorem laneV_top {MT M : Nat} (hT : IsTr MT M) (l : Nat) :
    laneV (appW NL ONES MT TSR (112 - 16) 16) l = vecJ (2 ^ 112 - 1) (laneV R l) M >>> 96 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [ONES_eq, TSR, testBit_laneV_appW hT wf_parts.1.2 96 16 l j (by omega), Nat.testBit_shiftRight]
  by_cases hj : j < 16
  · simp [hj]
  · rw [testBit_vecJ_ge _ _ (by omega)]
    simp [hj]

theorem tiesAt_eq (t : Nat) : tiesAt t = (TB.getD (t / 64) []).getD (t % 64) ([], []) := by
  rw [tiesAt, nthL_eq, nthL_eq]
  rfl

theorem canon_lane {t : Nat} (ht0 : 0 < t) (ht : t < 6720) {l : Nat} (hl : l < NL) :
    laneV R l ≤ vecJ rm (laneV R l) (CFSG.KD.X0O.MSF t) ∧
      (vecJ rm (laneV R l) (CFSG.KD.X0O.MSF t) = laneV R l ↔ l ∈ (tiesAt t).1) := by
  have hc := canon_ok t ht
  have hz : Nat.beq t 0 = false := by
    cases t with
    | zero => omega
    | succ n => rfl
  unfold canonF at hc
  rw [bIf_eq, hz] at hc
  simp only [Bool.false_eq_true, if_false] at hc
  obtain ⟨h1, h2⟩ := canonAt_spec hc
  have hlen : RT.length = (appW NL ONES (trJ t0 t1 t2 t3 t4 t5 t6 (CFSG.KD.X0O.MSF t)) TSR
      (112 - 16) 16).length := by
    rw [length_appW, RT, dropK_eq, List.length_drop, wf_parts.1.1]
  obtain ⟨c1, c2⟩ := cmpS_spec ONES _ _ hlen l
  rw [laneV_drop96, laneV_top (isTr_msf ht), ones_bit hl, Bool.true_and] at c1 c2
  have b1 := congrArg (fun x => x.testBit l) h1
  have b2 := congrArg (fun x => x.testBit l) h2
  simp only [Nat.testBit_or, c1, c2, ones_bit hl] at b1 b2
  rw [nlor, Nat.testBit_or, testBit_maskOf, testBit_maskOf] at b2
  have ht' := ties_ok t ht
  unfold tieF at ht'
  simp only [bAnd_eq, Bool.and_eq_true, allB_eq, List.all_eq_true, Nat.beq_eq] at ht'
  rw [rm_eq]
  set x := laneV R l
  set v := vecJ (2 ^ 112 - 1) x (CFSG.KD.X0O.MSF t)
  have hfirst : l ∈ (tiesAt t).1 → v = x := fun h => ht'.1 l h
  have hsecond : l ∈ (tiesAt t).2 → x < v := fun h => by
    have := ht'.2 l h
    rwa [Nat.blt_eq] at this
  have hsh : x >>> 96 < v >>> 96 → x < v := by
    intro h
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h
    by_contra hc
    exact absurd (Nat.div_le_div_right (c := 2 ^ 96) (Nat.le_of_not_lt hc)) (Nat.not_le_of_lt h)
  by_cases hf : l ∈ (tiesAt t).1
  · exact ⟨(hfirst hf).ge, ⟨fun _ => hf, fun _ => hfirst hf⟩⟩
  · by_cases hs : l ∈ (tiesAt t).2
    · exact ⟨(hsecond hs).le, ⟨fun h => absurd h (Nat.ne_of_gt (hsecond hs)), fun h => absurd h hf⟩⟩
    · have heq : ¬ x >>> 96 = v >>> 96 := by
        intro h
        rw [decide_eq_true h] at b2
        simp [hf, hs] at b2
      have hlt : x >>> 96 < v >>> 96 := by
        rw [decide_eq_false heq, Bool.or_false] at b1
        exact of_decide_eq_true b1
      exact ⟨(hsh hlt).le, ⟨fun h => absurd h (Nat.ne_of_gt (hsh hlt)), fun h => absurd h hf⟩⟩

@[expose] noncomputable def iterF (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ y => vecJ (2 ^ 112 - 1) y (getN one XG 0)) k

theorem iterF_succ (k x : Nat) : iterF (k + 1) x = vecJ (2 ^ 112 - 1) (iterF k x) (getN one XG 0) :=
  rfl

theorem startK_succ (k : Nat) : startK (k + 1) =
    appT (trJ t0 t1 t2 t3 t4 t5 t6 (getN one XG 0)) (tabsT (startK k) 28) 0 112 := rfl

theorem len_startK : ∀ k, (startK k).length = 112
  | 0 => wf_parts.1.1
  | k + 1 => by rw [startK_succ, length_appT]

theorem laneV_startK (l : Nat) : ∀ k, laneV (startK k) l = iterF k (laneV R l)
  | 0 => rfl
  | k + 1 => by rw [startK_succ, laneV_appT isTr_F, laneV_startK l k, iterF_succ]

noncomputable def bcF (ones v : Nat) (n : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun _ ih j => List.cons (nIf(Nat.beq (Nat.land (Nat.shiftRight v j) 1) 1, ones, 0))
      (ih (Nat.succ j))) n

theorem getD_bcF (ones v : Nat) : ∀ n j0 i, (bcF ones v n j0).getD i 0 =
    if i < n then (if v.testBit (j0 + i) then ones else 0) else 0
  | 0, _, i => by simp [bcF]
  | n + 1, j0, i => by
    change (List.cons (nIf(Nat.beq (Nat.land (Nat.shiftRight v j0) 1) 1, ones, 0))
      (bcF ones v n (j0 + 1))).getD i 0 = _
    cases i with
    | zero =>
      rw [List.getD_cons_zero, nIf_eq, nland, nshr, and_one_bit]
      cases v.testBit j0 <;> simp
    | succ i =>
      rw [List.getD_cons_succ, getD_bcF ones v n (j0 + 1) i, show j0 + 1 + i = j0 + (i + 1) by omega]
      by_cases h : i < n
      · simp [h, show i + 1 < n + 1 by omega]
      · simp [h, show ¬ i + 1 < n + 1 by omega]

theorem laneV_target0 {l : Nat} (hl : l < NL) : laneV (targetK 0) l = v2N rootV := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (laneV (bcF ONES (v2N rootV) 112 0) l).testBit j = _
  rw [testBit_laneV, getD_bcF, Nat.zero_add]
  by_cases hj : j < 112
  · rw [if_pos hj]
    cases h : (v2N rootV).testBit j
    · simp
    · simp [ones_bit hl]
  · have hr : rootV.wf = true := by decide
    rw [if_neg hj, Nat.zero_testBit,
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (v2N_lt112 hr)
        (Nat.pow_le_pow_right (n := 2) (by omega) (show 112 ≤ j by omega)))]

theorem laneV_target_succ (k l : Nat) : laneV (targetK (k + 1)) l = laneV (Z.getD k []) l := by
  change laneV (nthL [] Z k) l = _
  rw [nthL_eq]

theorem walk_lane {k : Nat} (hk : k < 5) {l : Nat} (hl : l < NL) :
    walkV Ai Bi B WS l (iterF k (laneV R l)) = laneV (targetK k) l := by
  have hw := walk_ok k hk
  unfold walkF at hw
  rw [eqL_iff, ONES_eq] at hw
  have h := (laneV_walkT isTr_Ai isTr_Bi isTr_B hl WS wf_parts.2.2.2 (startK k) (len_startK k)).2
  rw [hw, laneV_startK] at h
  exact h.symm

theorem getN_eq_getD (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, i + 1 => getN_eq_getD d t i

theorem getD_map_lt (f : Nat → Nat) {L : List Nat} {i : Nat} (h : i < L.length) :
    (L.map f).getD i 0 = f (L.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]

@[expose] noncomputable def Mf (j : Nat) : Nat := getN one Us j

theorem isTr_U {j : Nat} (hj : j < 11) : IsTr (UT.getD j 0) (Mf j) := by
  have hj' : j < Us.length := by rw [Us_length]; exact hj
  have e : UT.getD j 0 = trJ t0 t1 t2 t3 t4 t5 t6 (Mf j) := by
    change (mapS (trJ t0 t1 t2 t3 t4 t5 t6) Us).getD j 0 = _
    rw [mapS_eq, getD_map_lt _ hj', Mf, getN_eq_getD, List.getD_eq_getElem _ _ hj',
      List.getD_eq_getElem _ _ hj']
  rw [e]
  exact isTr_get (uTab_enc j hj')

theorem Zk_mem {k : Nat} (hk : k < 4) : Z.getD k [] ∈ Z := by
  rw [List.getD_eq_getElem _ _ (by rw [wf_parts.2.2.1]; exact hk)]
  exact List.getElem_mem _

theorem Zk_parts {k : Nat} (hk : k < 4) :
    (Z.getD k []).length = 112 ∧ ∀ j, (Z.getD k []).getD j 0 < 2 ^ NL := by
  obtain ⟨h1, h2⟩ := wf_parts.2.1 _ (Zk_mem hk)
  refine ⟨h1, fun j => ?_⟩
  rw [List.getD_eq_getElem?_getD]
  cases h : (Z.getD k [])[j]? with
  | none => exact Nat.two_pow_pos NL
  | some x => exact h2 x (List.mem_of_getElem? h)

theorem len_Z4 : Z4.length = 112 := by
  unfold Z4
  simp only [zipS_eq, mapS_eq, List.length_zipWith, List.length_map, nthL_eq,
    (Zk_parts (k := 0) (by omega)).1, (Zk_parts (k := 1) (by omega)).1,
    (Zk_parts (k := 2) (by omega)).1, (Zk_parts (k := 3) (by omega)).1]
  rfl

theorem laneV_Z4 {l : Nat} (hl : l < NL) {k : Nat} (hk : k < 4) :
    laneV Z4 (l + k * NL) = laneV (Z.getD k []) l := by
  apply Nat.eq_of_testBit_eq
  intro j
  have p0 := Zk_parts (k := 0) (by omega)
  have p1 := Zk_parts (k := 1) (by omega)
  have p2 := Zk_parts (k := 2) (by omega)
  have p3 := Zk_parts (k := 3) (by omega)
  rw [testBit_laneV, testBit_laneV]
  unfold Z4
  simp only [zipS_eq, mapS_eq, nthL_eq]
  rw [getD_zipWith0 (by rfl) _ _
      (by simp only [List.length_zipWith, List.length_map, p0.1, p1.1, p2.1, p3.1]),
    getD_zipWith0 (by rfl) _ _ (by simp only [List.length_map, p0.1, p1.1]),
    getD_zipWith0 (by rfl) _ _ (by simp only [List.length_map, p2.1, p3.1]),
    getD_map0 (by rfl), getD_map0 (by rfl), getD_map0 (by rfl)]
  simp only [nlor, nshl, nmul, Nat.testBit_or]
  rw [show l + k * NL = k * NL + l by omega, tb_blk0 (p0.2 j) hl, tb_blk1 (p1.2 j) hl,
    tb_blk (p2.2 j) hl, tb_blk (p3.2 j) hl]
  interval_cases k <;> simp

theorem etest_lane {l : Nat} (hl : l < NL) {a b : Nat} (ha : a < 32) (hb : b < 64)
    (hab : a ≠ 0 ∨ b ≠ 0)
    (heq : ∀ k < 4, prodV Mf 0 a 5 (laneV (Z.getD k []) l) = prodV Mf 5 b 6 (laneV (Z.getD k []) l)) :
    l ∈ DL := by
  have sA := subsT_spec (Ms := UT) (Mf := Mf) (j0 := 0) len_Z4 5
    (fun i hi => isTr_U (by omega))
  have sB := subsT_spec (Ms := UT) (Mf := Mf) (j0 := 5) len_Z4 6
    (fun i hi => isTr_U (by omega))
  have key : (pairFlags NL (2 ^ NL - 1) (2 ^ (4 * NL) - 1) 8 (subsT UT 0 5 Z4)
      (subsT UT 5 6 Z4)).testBit l = true := by
    refine pairFlags_of (a := a) (b := b) (by rw [sA.1]; exact ha) (by rw [sB.1]; exact hb) hab ?_
    refine agree4_of hl fun j _ k hk => ?_
    rw [← testBit_laneV, ← testBit_laneV, (sA.2 a ha).2, (sB.2 b hb).2, laneV_Z4 hl hk,
      heq k hk]
  have e : eFlags = pairFlags NL (2 ^ NL - 1) (2 ^ (4 * NL) - 1) 8 (subsT UT 0 5 Z4)
      (subsT UT 5 6 Z4) := by
    unfold eFlags
    rw [ONES_eq, ones4_eq]
  have hf : (eFlags).testBit l = true := e ▸ key
  have he := e_ok
  rw [Nat.beq_eq] at he
  have hb := congrArg (fun x => x.testBit l) he
  simp only [nland, nxor, Nat.testBit_and, Nat.testBit_xor, hf, ones_bit hl, Nat.zero_testBit,
    testBit_maskOf, Bool.true_and] at hb
  simpa using hb

theorem des_lane {l : Nat} (h : l ∈ DL) : l = LF ∨ ∃ j < 30, (WD.getD j (0, 0)).1 = l := by
  have hd := des_ok
  simp only [bAnd_eq, Bool.and_eq_true, allB_eq, List.all_eq_true, Nat.beq_eq, lenK_eq] at hd
  have h1 := hd.2.1 l h
  rw [bIf_eq] at h1
  by_cases hl : l = LF
  · exact Or.inl hl
  · right
    have hb : Nat.beq l LF = false := by
      cases h' : Nat.beq l LF
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') hl
    rw [hb, anyB_eq] at h1
    simp only [Bool.false_eq_true, if_false, List.any_eq_true, Nat.beq_eq] at h1
    obtain ⟨p, hp, hpl⟩ := h1
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hp
    refine ⟨j, by rw [← hd.2.2.2.1]; exact hj, ?_⟩
    rw [List.getD_eq_getElem _ _ hj]
    exact hpl

theorem lf_fix : vecJ (2 ^ 112 - 1) (laneV R LF) (getN one XG 0) = laneV R LF := by
  have hd := des_ok
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hd
  rw [← rm_eq]
  exact hd.2.2.1

theorem bnd_parts : (∀ p ∈ FXL, p.1 < NL ∧ p.2 < 6720) ∧ (∀ p ∈ WD, p.2 < 6720) ∧
    ∀ j < 30, D4.getD j 0 = v2N (CFSG.QuasithinUnique.A5.d4Reps[j]!) := by
  have h := bnd_ok
  simp only [bAnd_eq, Bool.and_eq_true, allB_eq, List.all_eq_true, Nat.blt_eq, Nat.beq_eq,
    List.mem_range, nthL_eq] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

theorem wit_lane {j : Nat} (hj : j < 30) :
    vecJ (2 ^ 112 - 1) (D4.getD j 0) (CFSG.KD.X0O.MSF (WD.getD j (0, 0)).2) =
      laneV R (WD.getD j (0, 0)).1 := by
  have h := wit_ok j hj
  unfold witF at h
  rw [Nat.beq_eq, nthL_eq, nthL_eq] at h
  rw [← rm_eq]
  exact h

theorem wd_lt {j : Nat} (hj : j < 30) : (WD.getD j (0, 0)).2 < 6720 := by
  have hl : WD.length = 30 := by
    have hd := des_ok
    simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq, lenK_eq] at hd
    exact hd.2.2.2.1
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hj)]
  exact bnd_parts.2.1 _ (List.getElem_mem _)

end CertificateChecks.KernelJ4Pent

end

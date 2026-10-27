module

public import Certificates.Kernel.MonsterExist.RigidW

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.RigidB

open CertificateChecks.MonsterExist.Sparse CertificateChecks.MonsterExist.RigidW
open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.AxisCount Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] noncomputable def bB (k : ℕ) : SpaceB := if k < 98580 then fbasis k else inW (wB (k - 98580))

theorem bB_eq (k : ℕ) (hk : k < 196884) : bB k = fbasis k := by
  unfold bB
  by_cases h : k < 98580
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, fbasis, ite_eq_right (by omega), ite_eq_right h, wvecB, wB, eRow,
      ite_eq_left (by omega)]

theorem bB_W (K : ℕ) : bB (98580 + K) = inW (wB K) := by
  unfold bB
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

@[expose] def shiftT (l : Terms) : Terms := l.map fun t => (98580 + t.1, t.2)

theorem sumT_shiftT (l : Terms) : sumT bB (shiftT l) = inW (sumT wB l) := by
  induction l with
  | nil => rfl
  | cons t l ih =>
    simp only [shiftT, List.map_cons, sumT_cons] at ih ⊢
    rw [ih, bB_W, smul_inW]
    simp

@[expose] def keyOdd (p : ℕ) : ℕ × ℕ :=
  (Model.oddCode (2 * ((p - 552) / 24)) ((p - 552) % 24),
    Model.thetaN (Model.oddCode (2 * ((p - 552) / 24)) ((p - 552) % 24)) ^^^
      Model.dualN (2 ^ ((p - 552) % 24)))

@[expose] def findOdd (a d : ℕ) : Option ℕ :=
  let t := (if a.testBit 0 then a ^^^ 63 else a) / 2
  let x := d ^^^ Model.thetaN a
  if t < 2048 then
    ((List.range 24).find? fun i => Model.dualN (2 ^ i) == x).bind fun i =>
      if keyOdd (552 + 24 * t + i) == (a, d) then some (552 + 24 * t + i) else none
  else none

theorem findOdd_spec {a d p : ℕ} (h : findOdd a d = some p) :
    552 ≤ p ∧ p < 49704 ∧ keyOdd p = (a, d) := by
  unfold findOdd at h
  dsimp only at h
  generalize (if a.testBit 0 = true then a ^^^ 63 else a) / 2 = t at h
  by_cases ht : t < 2048
  swap
  · rw [ite_eq_right ht] at h
    exact absurd h (by simp)
  rw [ite_eq_left ht] at h
  obtain ⟨i, hi, h3⟩ := Option.bind_eq_some_iff.1 h
  have h2 := List.mem_range.1 (List.mem_of_find?_eq_some hi)
  by_cases hk : (keyOdd (552 + 24 * t + i) == (a, d)) = true
  · rw [ite_eq_left hk, Option.some_inj] at h3
    subst h3
    exact ⟨by omega, by omega, by simpa using hk⟩
  · rw [ite_eq_right hk] at h3
    exact absurd h3 (by simp)

@[expose] def conjF : Native.Gen → Model.Pauli → Model.Pauli
  | .rho q => Model.conjPauliN q
  | .sign a => Model.conjYN a
  | .perm arr => Model.conjPermN arr
  | _ => id

@[expose] def isMono : Native.Gen → Bool
  | .rho _ => true
  | .sign _ => true
  | .perm _ => true
  | _ => false

theorem conjF_spec (g : Native.Gen) (hg : isMono g = true) (hv : g.validB = true) (y : Model.Pauli) :
    conjQ g.pair (pauliQ y) = pauliQ (conjF g y) := by
  cases g with
  | rho q => exact conjQ_rhoPair_toQ q y
  | sign a => exact conjQ_sign_toQ a y
  | perm arr => exact conjQ_perm_toQ (permOf arr) (permOf_spec hv) y
  | _ => simp [isMono] at hg

@[expose] def xCol (g : Native.Gen) (k : ℕ) : Terms :=
  match findOdd (conjF g (false, keyOdd (k - 300))).2.1 (conjF g (false, keyOdd (k - 300))).2.2 with
  | some p' => [(300 + p', Model.sgnI (conjF g (false, keyOdd (k - 300))).1)]
  | none => []

@[expose] def xOK (g : Native.Gen) (k : ℕ) : Bool :=
  isMono g && decide (852 ≤ k) && decide (k < 50004) &&
    (findOdd (conjF g (false, keyOdd (k - 300))).2.1 (conjF g (false, keyOdd (k - 300))).2.2).isSome

theorem toLin_eq (g : Native.Gen) (hg : isTau g = false) : g.toLin = thetaEquiv g.pair := by
  cases g with
  | tau => simp [isTau] at hg
  | _ => rfl

theorem xvec_of_key (p : ℕ) (h1 : 552 ≤ p) (h2 : p < 49704) :
    xvec p = inX (Xlift (pauliQ (false, (keyOdd p).1, (keyOdd p).2))) := by
  unfold xvec
  rw [keyOf_odd p h1 h2]
  rfl

theorem xCol_spec (g : Native.Gen) (hv : g.validB = true) (k : ℕ)
    (hk : xOK g k = true) : g.toLin (bB k) = ((1 : ℚ) / 2 ^ 0) • sumT bB (xCol g k) := by
  simp only [xOK, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hk
  obtain ⟨⟨⟨hm, hk1⟩, hk2⟩, p', hp'⟩ := hk
  obtain ⟨q1, q2, q3⟩ := findOdd_spec hp'
  have hg : isTau g = false := by cases g <;> simp_all [isMono, isTau]
  unfold xCol
  rw [hp']
  have hb : bB k = xvec (k - 300) := by
    rw [bB_eq k (by omega), show k = 300 + (k - 300) by omega, fbasis_X _ (by omega),
      Nat.add_sub_cancel_left]
  have hb' : bB (300 + p') = xvec p' := by rw [bB_eq (300 + p') (by omega), fbasis_X _ (by omega)]
  rw [hb, xvec_of_key _ (by omega) (by omega), toLin_eq g hg, thetaEquiv_apply, theta_apply]
  simp only [map_zero, thetaX_Xlift]
  rw [conjF_spec g hm hv, Xlift_pauliQ]
  simp only [sumT_cons, sumT_nil, add_zero, pow_zero, div_one, one_smul, hb',
    xvec_of_key p' q1 q2, q3]
  rw [sgn_boolZ, smul_inX]

@[expose] def tauCol (k : ℕ) : Terms :=
  if 852 ≤ k ∧ k < 50004 then
    [(98580 + 24 * (2048 + (k - 852) / 24) + (k - 852) % 24,
      8 * Native.sgnI ((Native.wordN (2 * ((k - 852) / 24))).testBit ((k - 852) % 24)))]
  else if 98580 ≤ k ∧ k < 98580 + 24 * 2048 then
    [(852 + 24 * ((k - 98580) / 24) + (k - 98580) % 24,
      8 * Native.sgnI (Native.pN (2 * ((k - 98580) / 24))))]
  else
    [(98580 + 24 * ((k - 98580) / 24 - 2048) + (k - 98580) % 24,
      8 * Native.sgnI ((Native.wordN (2 * ((k - 98580) / 24 - 2048))).testBit ((k - 98580) % 24)) *
        Native.sgnI (Native.pN (2 * ((k - 98580) / 24 - 2048))))]

@[expose] def tauOK (k : ℕ) : Bool :=
  decide (852 ≤ k) && decide (k < 196884) && !(decide (50004 ≤ k) && decide (k < 98580))

theorem tauCol_eq (k : ℕ) (hk : tauOK k = true) : tauCol k = tauL k := by
  simp only [tauOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at hk
  obtain ⟨⟨h1, h2⟩, h3⟩ := hk
  unfold tauCol
  by_cases a1 : 852 ≤ k ∧ k < 50004
  · rw [ite_eq_left a1]
    have e : k = 852 + 24 * ((k - 852) / 24) + (k - 852) % 24 := by omega
    conv_rhs => rw [e]
    rw [tauL_odd _ _ (by omega) (Nat.mod_lt _ (by norm_num))]
  · rw [ite_eq_right a1]
    by_cases a2 : 98580 ≤ k ∧ k < 98580 + 24 * 2048
    · rw [ite_eq_left a2]
      have e : k = 98580 + 24 * ((k - 98580) / 24) + (k - 98580) % 24 := by omega
      conv_rhs => rw [e]
      rw [tauL_Wlo _ _ (by omega) (Nat.mod_lt _ (by norm_num))]
    · rw [ite_eq_right a2]
      have e : k = 98580 + 24 * (2048 + ((k - 98580) / 24 - 2048)) + (k - 98580) % 24 := by omega
      conv_rhs => rw [e]
      rw [tauL_Whi _ _ (by omega) (Nat.mod_lt _ (by norm_num))]

theorem tauCol_spec (k : ℕ) (hk : tauOK k = true) :
    tauB (bB k) = ((1 : ℚ) / 2 ^ 3) • sumT bB (tauCol k) := by
  have hk' : k < 196884 := by
    simp only [tauOK, Bool.and_eq_true, decide_eq_true_eq] at hk
    exact hk.1.2
  rw [bB_eq k hk', tauBasis k hk', tauCol_eq k hk]
  have h : sumT bB (tauL k) = sumT fbasis (tauL k) := by
    have hl := tauL_lt k hk'
    unfold sumT
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [bB_eq t.1 (hl t ht)]
  rw [h]
  norm_num
  rfl

@[expose] def colB : Native.Gen → ℕ → Terms
  | .tau, k => tauCol k
  | g, k => if 98580 ≤ k then shiftT (colW g (k - 98580)) else xCol g k

@[expose] def okB : Native.Gen → ℕ → Bool
  | .tau, k => tauOK k
  | g, k => if 98580 ≤ k then okW g (k - 98580) else xOK g k

@[expose] def exB : Native.Gen → ℕ
  | .tau => 3
  | g => exW g

theorem exW_mono (g : Native.Gen) (hg : isMono g = true) : exW g = 0 := by
  cases g <;> simp_all [isMono, exW, rowE, latE]

theorem colB_spec (g : Native.Gen) (hv : g.validB = true) (k : ℕ)
    (hk : okB g k = true) : g.toLin (bB k) = ((1 : ℚ) / 2 ^ exB g) • sumT bB (colB g k) := by
  by_cases ht : isTau g = true
  · cases g <;> simp [isTau] at ht
    exact tauCol_spec k hk
  · rw [Bool.not_eq_true] at ht
    have hcol : colB g k = if 98580 ≤ k then shiftT (colW g (k - 98580)) else xCol g k := by
      cases g <;> simp_all [isTau, colB]
    have hok : okB g k = if 98580 ≤ k then okW g (k - 98580) else xOK g k := by
      cases g <;> simp_all [isTau, okB]
    have hex : exB g = exW g := by cases g <;> simp_all [isTau, exB]
    rw [hcol, hex]
    rw [hok] at hk
    by_cases hW : 98580 ≤ k
    · rw [ite_eq_left hW] at hk ⊢
      have e : bB k = inW (wB (k - 98580)) := by
        rw [show k = 98580 + (k - 98580) by omega, bB_W, Nat.add_sub_cancel_left]
      rw [e, sumT_shiftT, toLin_eq g ht, thetaEquiv_apply, theta_apply]
      simp only [map_zero]
      rw [smul_inW]
      exact congrArg inW (semW_wB g ht hv _ hk)
    · rw [ite_eq_right hW] at hk ⊢
      have hm : isMono g = true := by
        simp only [xOK, Bool.and_eq_true] at hk
        exact hk.1.1.1
      rw [exW_mono g hm]
      exact xCol_spec g hv k hk

theorem wordLin_eq_foldl (w : List Native.Gen) (x : SpaceB) :
    wordLin w x = w.foldl (fun x g => g.toLin.toLinearMap x) x := by
  induction w generalizing x with
  | nil => rfl
  | cons g w ih => rw [wordLin_apply_cons, ih, List.foldl_cons]; rfl

theorem wordLin_bB (w : List Native.Gen)
    (hw : ∀ g ∈ w, g.validB = true) (k : ℕ)
    (h : (runT okB colB exB w (true, 0, [(k, 1)])).1 = true) :
    wordLin w (bB k) = ((1 : ℚ) / 2 ^ (runT okB colB exB w (true, 0, [(k, 1)])).2.1) •
      sumT bB (runT okB colB exB w (true, 0, [(k, 1)])).2.2 := by
  have h1 := runT_sound bB (fun g => g.toLin.toLinearMap) okB colB exB w
    (fun g hg k hk => colB_spec g (hw g hg) k hk) 0 [(k, 1)] h
  rw [← h1, wordLin_eq_foldl]
  simp [sumT]

theorem eqv_of_cf {v w : Native.DVec} (hv : v.D.size = 196884) (hw : w.D.size = 196884)
    (h : ∀ k < 196884, cf v k = cf w k) : v.eqv w = true := by
  unfold Native.DVec.eqv
  rw [beq_iff_eq]
  have key : ∀ k < 196884, (Native.scale (max v.e w.e - v.e) v.D).getD k 0 =
      (Native.scale (max v.e w.e - w.e) w.D).getD k 0 := by
    intro k hk
    rw [Native.scale_getD _ _ _ (by rw [hv]; exact hk), Native.scale_getD _ _ _ (by rw [hw]; exact hk)]
    have he := h k hk
    unfold cf at he
    have h2 : ((v.D.getD k 0 * 2 ^ (max v.e w.e - v.e) : ℤ) : ℚ) =
        ((w.D.getD k 0 * 2 ^ (max v.e w.e - w.e) : ℤ) : ℚ) := by
      push_cast
      have p1 : (2 : ℚ) ^ (max v.e w.e - v.e) = 2 ^ max v.e w.e / 2 ^ v.e := by
        rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
      have p2 : (2 : ℚ) ^ (max v.e w.e - w.e) = 2 ^ max v.e w.e / 2 ^ w.e := by
        rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel (le_max_right _ _)]
      rw [p1, p2, mul_div_assoc', mul_div_assoc', mul_comm, mul_div_assoc, he, ← mul_div_assoc,
        mul_comm]
    exact_mod_cast h2
  apply Array.ext
  · rw [Native.scale_size, Native.scale_size, hv, hw]
  · intro i h1 h2
    have hi : i < 196884 := by rw [Native.scale_size, hv] at h1; exact h1
    have := key i hi
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

theorem eqv_of_interp {v w : Native.DVec} (hv : v.D.size = 196884)
    (hw : w.D.size = 196884) (h : interp v = interp w) : v.eqv w = true := by
  have hA : interpA v = interpA w := congrArg Prod.fst h
  have hX : interpX v = interpX w := congrArg (fun x : SpaceB => x.2.1) h
  have hW : interpW v = interpW w := congrArg (fun x : SpaceB => x.2.2) h
  refine eqv_of_cf hv hw fun k hk => ?_
  by_cases h1 : k < 300
  · obtain ⟨a1, a2⟩ := aPos_lt k h1
    have e := congrArg (fun A : symMat => (A : Matrix (Fin 24) (Fin 24) ℚ)
      (finOf (Native.aPos k).1) (finOf (Native.aPos k).2)) hA
    simp only [interpA, of_apply, finOf_val _ a1, finOf_val _ a2, aIdx_aPos k h1] at e
    exact e
  by_cases h2 : k < 98580
  · have e := congrFun hX (shortOf ⟨k - 300, by omega⟩)
    simp only [interpX, posOf_shortOf] at e
    rw [show 300 + (k - 300) = k by omega] at e
    exact e
  · have hr : (k - 98580) / 24 < 4096 := by omega
    have hj : (k - 98580) % 24 < 24 := Nat.mod_lt _ (by norm_num)
    have e := congrFun (congrFun hW (spinOfRow ((k - 98580) / 24))) (finOf ((k - 98580) % 24))
    simp only [interpW, of_apply, rowOf_spinOfRow hr, finOf_val _ hj] at e
    rw [show 98580 + 24 * ((k - 98580) / 24) + (k - 98580) % 24 = k by omega] at e
    exact e

theorem reduceN_size : ∀ (n : ℕ) (v : Native.DVec), (Native.reduceN n v).D.size = v.D.size
  | 0, _ => rfl
  | n + 1, v => by
    unfold Native.reduceN
    split_ifs
    · rw [reduceN_size n]
      simp
    · rfl

theorem applyGen_size (c : Native.Ctx) (g : Native.Gen) (v : Native.DVec) :
    (Native.applyGen c g v).D.size = 196884 := by
  cases g with
  | tau =>
    have e : Native.applyGen c .tau v = Native.applyTau c v := rfl
    rw [e, applyTau_D, Native.scatterAt_size]
  | _ =>
    change (Native.scale _ (Native.latA _ v.D) ++ Native.scale _ (Native.scatterAt 300 98280 _ v.D) ++
      Native.scale _ (Native.scatterAt 0 98304 _ (Native.wMul _ v.D))).size = _
    simp only [Array.size_append, Native.scale_size, Native.latA_size, Native.scatterAt_size]

theorem evalWordC_size (c : Native.Ctx) :
    ∀ (w : List Native.Gen) (v : Native.DVec), v.D.size = 196884 →
      (Native.evalWordC c w v).D.size = 196884
  | [], _, h => h
  | g :: w, v, _ => by
    rw [evalWordC_cons]
    refine evalWordC_size c w _ ?_
    rw [Native.DVec.reduce, reduceN_size, applyGen_size]

@[expose] def rigidB (w₁ w₂ : List Native.Gen) : Bool :=
  CFSG.Monster.Existence.Census.rigidKeys.all fun k =>
    pairOK (runT okB colB exB w₁ (true, 0, [(98580 + keyW k, 1)]))
      (runT okB colB exB w₂ (true, 0, [(98580 + keyW k, 1)]))

@[expose] def checkB (w₁ w₂ : List Native.Gen) : Bool :=
  (w₁ ++ w₂).all (fun g => g.validB) && rigidB w₁ w₂

theorem checkRigid_of_checkB {w₁ w₂ : List Native.Gen}
    (h : checkB w₁ w₂ = true) :
    CFSG.Monster.Existence.Census.checkRigid (Native.mkCtx ()) w₁ w₂ = true := by
  simp only [checkB, Bool.and_eq_true] at h
  obtain ⟨hv, hr⟩ := h
  have hg1 : ∀ g ∈ w₁, g.validB = true := fun g h => List.all_eq_true.1 hv g (List.mem_append_left _ h)
  have hg2 : ∀ g ∈ w₂, g.validB = true := fun g h => List.all_eq_true.1 hv g (List.mem_append_right _ h)
  unfold CFSG.Monster.Existence.Census.checkRigid
  rw [hv, Bool.true_and]
  refine List.all_eq_true.2 fun k hk => ?_
  have hk' := List.all_eq_true.1 hr k hk
  have hs : (CFSG.Monster.Existence.Census.rigidDVec k).D.size = 196884 := by
    unfold CFSG.Monster.Existence.Census.rigidDVec
    have := keyW_lt k
    unfold keyW at this
    simp [Native.DVec.ofList, Native.DVec.ofListE, show 98580 + 24 * Native.rowIdx k.1 k.2.1 + k.2.2 < 196884
      by omega]
  refine eqv_of_interp (evalWordC_size _ w₁ _ hs) (evalWordC_size _ w₂ _ hs) ?_
  have hb : interp (CFSG.Monster.Existence.Census.rigidDVec k) = bB (98580 + keyW k) := by
    have hlt : 98580 + keyW k < 196884 := by
      have := keyW_lt k
      omega
    rw [CFSG.Monster.Existence.Census.interp_rigidDVec, ← CFSG.Monster.Existence.Census.fbasis_rowIdx,
      bB_eq _ hlt]
    unfold keyW
    rw [Nat.add_assoc]
  rw [evalWordC_sound w₁ hg1, evalWordC_sound w₂ hg2, hb]
  revert hk'
  unfold pairOK
  generalize e1 : runT okB colB exB w₁ (true, 0, [(98580 + keyW k, 1)]) = s₁
  generalize e2 : runT okB colB exB w₂ (true, 0, [(98580 + keyW k, 1)]) = s₂
  obtain ⟨f₁, x₁, l₁⟩ := s₁
  obtain ⟨f₂, x₂, l₂⟩ := s₂
  intro hk'
  simp only [Bool.and_eq_true] at hk'
  obtain ⟨⟨hf1, hf2⟩, heq⟩ := hk'
  have r1 := wordLin_bB w₁ hg1 _ (by rw [e1]; exact hf1)
  have r2 := wordLin_bB w₂ hg2 _ (by rw [e2]; exact hf2)
  rw [e1] at r1
  rw [e2] at r2
  rw [r1, r2]
  exact smul_sumT_eq_of_eqT bB heq

end CertificateChecks.MonsterExist.RigidB

module

public import Certificates.Kernel.MonsterExist.ELevel.Pauli
public import Certificates.Kernel.MonsterExist.Eb.Sound

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ELevel

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Existence CFSG.Monster.B.TwoA.Census CertificateChecks.MonsterExist.ShortKey
  CertificateChecks.MonsterExist.Eb

theorem checkX_of {sl : List ℕ} {tt td : Array Model.Pauli} {xw : ℕ} {PIV : List (ℕ × ℕ)}
    {FB : List ℕ} {MV MS : ℕ → Prop} (he : elim tt td = (PIV, FB))
    (h1 : ∀ f ∈ FB, kapX tt td f = f)
    (hb : ∀ xv ∈ sl, kapX tt td xv = xv → MV xv)
    (hc : ∀ xS ∈ sl, (FB.all fun f => !bX f (xS ^^^ xw)) = true → MS xS)
    (hd : ∀ xv, MV xv → ∀ xS, MS xS → (bX xS xv || !isShortX (xS ^^^ xv) ||
      (match solveX PIV xv with
        | none => false
        | some u => MX tt td u == xv && (bX (xS ^^^ xw) u != csX tt td xv))) = true) :
    checkX sl tt td xw = true := by
  unfold checkX
  simp only [he, Bool.and_eq_true, List.all_eq_true, List.mem_filter, beq_iff_eq]
  refine ⟨h1, fun xv hxv xS hxS => ?_⟩
  exact hd xv (hb xv hxv.1 hxv.2) xS (hc xS hxS.1 (List.all_eq_true.2 hxS.2))

theorem parN_xor (k a b : ℕ) : Model.parN k (a ^^^ b) = (Model.parN k a ^^ Model.parN k b) := by
  rw [parN_eq, parN_eq, parN_eq, ← xorSum_xor]
  congr 1
  funext i
  rw [Nat.testBit_xor]

theorem pairN_xor_right (a d e : ℕ) : Model.pairN a (d ^^^ e) = (Model.pairN a d ^^ Model.pairN a e) := by
  unfold Model.pairN
  rw [Nat.and_xor_distrib_left, parN_xor]

theorem pairN_xor_left (a b d : ℕ) : Model.pairN (a ^^^ b) d = (Model.pairN a d ^^ Model.pairN b d) := by
  unfold Model.pairN
  rw [Nat.and_xor_distrib_right, parN_xor]

theorem bX_xor (f a b : ℕ) : bX f (a ^^^ b) = (bX f a ^^ bX f b) := by
  unfold bX
  rw [Nat.shiftRight_xor_distrib, pairN_xor_right, pairN_xor_left]
  cases Model.pairN f (a >>> 12) <;> cases Model.pairN f (b >>> 12) <;>
    cases Model.pairN a (f >>> 12) <;> cases Model.pairN b (f >>> 12) <;> rfl

theorem synL_cons (f : ℕ) (FB : List ℕ) (y : ℕ) : synL (f :: FB) y = bXK f y + 2 * synL FB y := rfl

theorem synL_xor (FB : List ℕ) (a b : ℕ) : synL FB (a ^^^ b) = synL FB a ^^^ synL FB b := by
  induction FB with
  | nil =>
    change 0 = 0 ^^^ 0
    rw [Nat.zero_xor]
  | cons f FB ih =>
    rw [synL_cons, synL_cons, synL_cons, ih, bXK_eq, bXK_eq, bXK_eq, bX_xor]
    generalize synL FB a = u
    generalize synL FB b = v
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_xor]
    rcases i with _ | i
    · cases bX f a <;> cases bX f b <;> simp [Nat.testBit_zero]
    · have e : ∀ (c : Bool) (w : ℕ), (c.toNat + 2 * w).testBit (i + 1) = w.testBit i := by
        intro c w
        rw [Nat.testBit_succ]
        congr 1
        cases c <;> simp
        all_goals omega
      rw [e, e, e, Nat.testBit_xor]

theorem synL_lt (FB : List ℕ) (y : ℕ) : synL FB y < 2 ^ FB.length := by
  induction FB with
  | nil => exact Nat.one_pos
  | cons f FB ih =>
    rw [synL_cons, List.length_cons, Nat.pow_succ, bXK_eq]
    cases bX f y <;> simp <;> omega

theorem synL_eq_zero (FB : List ℕ) (y : ℕ) :
    synL FB y = 0 ↔ (FB.all fun f => !bX f y) = true := by
  induction FB with
  | nil => simp [synL]
  | cons f FB ih =>
    rw [synL_cons, List.all_cons, Bool.and_eq_true, ← ih, bXK_eq]
    cases bX f y <;> simp

theorem xorFoldN_xor (B x y lo : ℕ) : ∀ n, xorFoldN B (x ^^^ y) lo n = xorFoldN B x lo n ^^^ xorFoldN B y lo n
  | 0 => by
    change 0 = 0 ^^^ 0
    rw [Nat.zero_xor]
  | n + 1 => by
    rw [xorFoldN_succ, xorFoldN_succ, xorFoldN_succ, xorFoldN_xor B x y lo n, Nat.shiftRight_xor_distrib,
      Nat.testBit_xor]
    generalize xorFoldN B x lo n = u
    generalize xorFoldN B y lo n = v
    cases (x >>> lo).testBit n <;> cases (y >>> lo).testBit n <;> simp [Nat.xor_assoc, Nat.xor_comm,
      Nat.xor_left_comm]

theorem kapL_xor (TB DB x y : ℕ) : kapL TB DB (x ^^^ y) = kapL TB DB x ^^^ kapL TB DB y := by
  unfold kapL
  change (xorFold TB (x ^^^ y) 0 ^^^ xorFold DB (x ^^^ y) 12) &&& (2 ^ 24 - 1) =
    ((xorFold TB x 0 ^^^ xorFold DB x 12) &&& (2 ^ 24 - 1)) ^^^
      ((xorFold TB y 0 ^^^ xorFold DB y 12) &&& (2 ^ 24 - 1))
  rw [xorFold_eq, xorFold_eq, xorFold_eq, xorFold_eq, xorFold_eq, xorFold_eq, xorFoldN_xor, xorFoldN_xor,
    ← Nat.and_xor_distrib_right]
  congr 1
  simp only [Nat.xor_assoc, Nat.xor_left_comm]

theorem kapL_lt (TB DB x : ℕ) : kapL TB DB x < 2 ^ 24 := by
  unfold kapL
  change _ &&& (2 ^ 24 - 1) < _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (by positivity)

theorem tPoint_eq (j b : ℕ) (hb : b < 256) : tPoint (256 * j + b) = b <<< (8 * j) := by
  unfold tPoint
  change ((256 * j + b) &&& 255) <<< (8 * ((256 * j + b) >>> 8)) = _
  have e1 : (256 * j + b) &&& 255 = b := by
    rw [show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : (256 * j + b) >>> 8 = j := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2]

@[expose] noncomputable def Fv (TB DB : ℕ) (FB : List ℕ) (y : ℕ) : ℕ :=
  kapL TB DB y ||| (synL FB y <<< 24)

theorem lane40_eq {TB DB TT : ℕ} {FB : List ℕ} (h : ttOK TB DB FB TT = true) {e : ℕ} (he : e < 768) :
    laneW 40 TT e = Fv TB DB FB (tPoint e) :=
  beq_true.1 ((allN_iff _ _).1 h e he)

theorem or_shift_xor {k k' s s' : ℕ} (hk : k < 2 ^ 24) (hk' : k' < 2 ^ 24) :
    (k ||| (s <<< 24)) ^^^ (k' ||| (s' <<< 24)) = (k ^^^ k') ||| ((s ^^^ s') <<< 24) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : 24 ≤ i
  · have h1 : k.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hi))
    have h2 : k'.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hk' (Nat.pow_le_pow_right (by norm_num) hi))
    simp [hi, h1, h2]
  · simp [hi]

theorem Fv_xor (TB DB : ℕ) (FB : List ℕ) (a b : ℕ) :
    Fv TB DB FB a ^^^ Fv TB DB FB b = Fv TB DB FB (a ^^^ b) := by
  unfold Fv
  rw [or_shift_xor (kapL_lt _ _ _) (kapL_lt _ _ _), kapL_xor, synL_xor]

theorem bytes_split {x : ℕ} (hx : x < 2 ^ 24) :
    (x &&& 255) <<< (8 * 0) ^^^ (((x >>> 8) &&& 255) <<< (8 * 1) ^^^ ((x >>> 16) &&& 255) <<< (8 * 2)) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_shiftRight,
    show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < 8
  · simp [h1, show ¬ 8 ≤ i by omega, show ¬ 16 ≤ i by omega]
  · by_cases h2 : i < 16
    · simp [h1, show 8 ≤ i by omega, show ¬ 16 ≤ i by omega, show i - 8 < 8 by omega,
        show 8 + (i - 8) = i by omega]
    · by_cases h3 : i < 24
      · simp [h1, show 8 ≤ i by omega, show 16 ≤ i by omega, show ¬ i - 8 < 8 by omega,
          show i - 16 < 8 by omega, show 16 + (i - 16) = i by omega]
      · have hb : x.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, show 8 ≤ i by omega, show 16 ≤ i by omega, show ¬ i - 8 < 8 by omega,
          show ¬ i - 16 < 8 by omega, hb]

theorem and255_lt (y : ℕ) : y &&& 255 < 256 := lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem tabK_eq {TB DB TT : ℕ} {FB : List ℕ} (h : ttOK TB DB FB TT = true) {x : ℕ} (hx : x < 2 ^ 24) :
    tabK TT x = Fv TB DB FB x := by
  have l0 := lane40_eq h (e := 256 * 0 + (x &&& 255)) (by have := and255_lt x; omega)
  have l1 := lane40_eq h (e := 256 * 1 + ((x >>> 8) &&& 255)) (by have := and255_lt (x >>> 8); omega)
  have l2 := lane40_eq h (e := 256 * 2 + ((x >>> 16) &&& 255)) (by have := and255_lt (x >>> 16); omega)
  rw [tPoint_eq _ _ (and255_lt _)] at l0 l1 l2
  have e0 : 256 * 0 + (x &&& 255) = x &&& 255 := by omega
  have e1 : 256 * 1 + ((x >>> 8) &&& 255) = 256 + ((x >>> 8) &&& 255) := by omega
  have e2 : 256 * 2 + ((x >>> 16) &&& 255) = 512 + ((x >>> 16) &&& 255) := by omega
  rw [e0] at l0
  rw [e1] at l1
  rw [e2] at l2
  change laneW 40 TT (x &&& 255) ^^^ laneW 40 TT (256 + ((x >>> 8) &&& 255)) ^^^
    laneW 40 TT (512 + ((x >>> 16) &&& 255)) = _
  rw [l0, l1, l2, Nat.xor_assoc, Fv_xor, Fv_xor, bytes_split hx]

theorem Fv_low (TB DB : ℕ) (FB : List ℕ) (y : ℕ) : Fv TB DB FB y % 2 ^ 24 = kapL TB DB y := by
  unfold Fv
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 24
  · simp [hi, show ¬ 24 ≤ i by omega]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (kapL_lt TB DB y)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hi]

theorem Fv_high (TB DB : ℕ) (FB : List ℕ) (y : ℕ) : Fv TB DB FB y >>> 24 = synL FB y := by
  unfold Fv
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le (kapL_lt TB DB y) (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  simp [show 24 + i - 24 = i by omega]

theorem bucketAll_sound (P : ℕ → Bool) (h : ∀ a < 4096, bucketAll P a = true) :
    ∀ x ∈ keyList, P x = true := by
  intro x hx
  obtain ⟨a, ha, k, hk, rfl⟩ := mem_keyList_iff.1 hx
  have hc := h a ha
  unfold bucketAll at hc
  have hc2 := (allN_iff _ _).1 hc k hk
  rw [laneW_slice SKV (offB (bkt a)) (cntB (bkt a)) k hk] at hc2
  exact hc2

theorem passRange_iff (P : ℕ → Bool) (lo n : ℕ) :
    passRange P lo n = true ↔ ∀ k < n, bucketAll P (lo + k) = true :=
  allN_iff (fun k => bucketAll P (Nat.add lo k)) n

theorem bNot_of {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

theorem lanes_mem {n L x : ℕ} (hL : L < 2 ^ (25 * n)) (hl : ∀ t < n, laneW 25 L t < 2 ^ 24)
    (hx : x < 2 ^ 24) (h : absentL 25 n L x = false) : ∃ t < n, laneW 25 L t = x := by
  have := absentL_iff (W := 25) (n := n) (v := L) (d := x) (by norm_num) hL hl hx
  rw [← Bool.not_eq_true, this] at h
  simp only [not_forall, not_not, exists_prop] at h
  exact h

theorem land24 (t : ℕ) : Nat.land t (nat_lit 16777215) = t % 2 ^ 24 :=
  Nat.and_two_pow_sub_one_eq_mod t 24

theorem passT_spec {TB DB TT sw nCV CV nCS CS : ℕ} {FB : List ℕ} (htt : ttOK TB DB FB TT = true)
    (hcv : CV < 2 ^ (25 * nCV) ∧ ∀ t < nCV, laneW 25 CV t < 2 ^ 24)
    (hcs : CS < 2 ^ (25 * nCS) ∧ ∀ t < nCS, laneW 25 CS t < 2 ^ 24) {x : ℕ} (hx : x < 2 ^ 24)
    (h : passT TT sw nCV CV nCS CS x = true) :
    (kapL TB DB x = x → ∃ t < nCV, laneW 25 CV t = x) ∧
      (synL FB x = sw → ∃ t < nCS, laneW 25 CS t = x) := by
  unfold passT at h
  rw [tabK_eq htt hx] at h
  change bAnd(bIf(Nat.beq (Nat.land (Fv TB DB FB x) (nat_lit 16777215)) x, bIf(absentL 25 nCV CV x, false, true), true),
    bIf(Nat.beq (Fv TB DB FB x >>> 24) sw, bIf(absentL 25 nCS CS x, false, true), true)) = true at h
  rw [land24, Fv_low, Fv_high, bAnd_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hk => ?_, fun hs => ?_⟩
  · rw [hk, show Nat.beq x x = true from beq_true.2 rfl] at h1
    exact lanes_mem hcv.1 hcv.2 hx (bNot_of h1)
  · rw [hs, show Nat.beq sw sw = true from beq_true.2 rfl] at h2
    exact lanes_mem hcs.1 hcs.2 hx (bNot_of h2)

theorem bitN_le1 (x i : ℕ) : bitN x i = 0 ∨ bitN x i = 1 := by
  rw [bitN_eq]
  cases x.testBit i <;> simp

theorem csK_le1 (TB DB x : ℕ) : csK TB DB x = 0 ∨ csK TB DB x = 1 := bitN_le1 _ _

theorem third_eq (TB DB xw v s : ℕ) (su : Option ℕ) (tt td : Array Model.Pauli)
    (hk : ∀ u, kapX tt td u = kapL TB DB u) (hc : csX tt td v = (csK TB DB v == 1)) :
    (match su with
      | none => false
      | some u => MX tt td u == v && (bX (s ^^^ xw) u != csX tt td v)) =
      thirdK TB DB xw v su (csK TB DB v) s := by
  cases su with
  | none => rfl
  | some u =>
    unfold thirdK
    change (MX tt td u == v && (bX (s ^^^ xw) u != csX tt td v)) =
      bAnd(Nat.beq (Nat.xor u (kapL TB DB u)) v, bIf(Nat.beq (bXK (Nat.xor s xw) u) (csK TB DB v), false, true))
    rw [bXK_eq, hc]
    unfold MX
    rw [hk u]
    change ((u ^^^ kapL TB DB u) == v && (bX (s ^^^ xw) u != (csK TB DB v == 1))) =
      bAnd(Nat.beq (u ^^^ kapL TB DB u) v, bIf(Nat.beq (bX (s ^^^ xw) u).toNat (csK TB DB v), false, true))
    have hbe : (u ^^^ kapL TB DB u == v) = Nat.beq (u ^^^ kapL TB DB u) v := rfl
    rw [hbe]
    rcases csK_le1 TB DB v with e | e <;> rw [e] <;> cases bX (s ^^^ xw) u <;>
      cases Nat.beq (u ^^^ kapL TB DB u) v <;> rfl

theorem inner_spec {TB DB xw v s : ℕ} {PIV : List (ℕ × ℕ)} {su : Option ℕ}
    {tt td : Array Model.Pauli} (hk : ∀ u, kapX tt td u = kapL TB DB u)
    (hc : csX tt td v = (csK TB DB v == 1)) (hsu : solveX PIV v = su) (hv : v < 2 ^ 24) (hs : s < 2 ^ 24)
    (h : innerP TB DB xw v su (csK TB DB v) s = true) :
    (bX s v || !isShortX (s ^^^ v) ||
      (match solveX PIV v with
        | none => false
        | some u => MX tt td u == v && (bX (s ^^^ xw) u != csX tt td v))) = true := by
  rw [hsu, third_eq TB DB xw v s su tt td hk hc, ← memK_eq_isShortX (Nat.xor_lt_two_pow hs hv)]
  unfold innerP at h
  change bIf(Nat.beq (bXK s v) 1, true, bIf(memK (s ^^^ v), thirdK TB DB xw v su (csK TB DB v) s, true)) = true at h
  rw [bXK_eq, beq_one_toNat] at h
  revert h
  cases bX s v <;> cases memK (s ^^^ v) <;> cases thirdK TB DB xw v su (csK TB DB v) s <;> decide

theorem checkX_of_kernel {i TB DB TT sw nCV CV nCS CS xw : ℕ}
    {PIV : List (ℕ × ℕ)} {FB : List ℕ} (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i))
    (hb : BasisOK i TB DB) (htt : ttOK TB DB FB TT = true) (hxw : packP (wP i) = xw)
    (hsw : synL FB xw = sw) (helim : elimGo (fun x => x ^^^ kapL TB DB x) 24 [] [] = (PIV, FB))
    (hfb : ∀ f ∈ FB, kapL TB DB f = f)
    (hpass : ∀ a < 4096, bucketAll (passT TT sw nCV CV nCS CS) a = true)
    (hcv : CV < 2 ^ (25 * nCV) ∧ ∀ t < nCV, laneW 25 CV t < 2 ^ 24)
    (hcs : CS < 2 ^ (25 * nCS) ∧ ∀ t < nCS, laneW 25 CS t < 2 ^ 24)
    (hin : ∀ t < nCV, innerV TB DB PIV xw nCS CS (laneW 25 CV t) = true) :
    checkX shortPacked (tT i) (tD i) (packP (wP i)) = true := by
  have hk : ∀ u, kapX (tT i) (tD i) u = kapL TB DB u := kapX_eq_kapL h1 h2 hb
  have hMX : MX (tT i) (tD i) = fun x => x ^^^ kapL TB DB x := by
    funext x
    unfold MX
    rw [hk]
  have he : elim (tT i) (tD i) = (PIV, FB) := by
    unfold elim
    rw [hMX]
    exact helim
  rw [hxw]
  refine checkX_of (MV := fun v => ∃ t < nCV, laneW 25 CV t = v)
    (MS := fun s => ∃ t < nCS, laneW 25 CS t = s) he (fun f hf => by rw [hk]; exact hfb f hf) ?_ ?_ ?_
  · intro xv hxv hfix
    obtain ⟨hx24, hm⟩ := mem_shortPacked_iff_memK.1 hxv
    have hp := bucketAll_sound _ hpass xv ((memK_iff_mem bucket_ok hx24).1 hm)
    exact (passT_spec htt hcv hcs hx24 hp).1 (by rw [← hk]; exact hfix)
  · intro xS hxS horth
    obtain ⟨hx24, hm⟩ := mem_shortPacked_iff_memK.1 hxS
    have hp := bucketAll_sound _ hpass xS ((memK_iff_mem bucket_ok hx24).1 hm)
    refine (passT_spec htt hcv hcs hx24 hp).2 ?_
    have h0 := (synL_eq_zero FB (xS ^^^ xw)).2 horth
    rw [synL_xor, hsw] at h0
    exact (xor_eq_zero_iff'.1 h0)
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨r, hr, rfl⟩
    have hv := hin t ht
    unfold innerV at hv
    have hr' := (allN_iff _ _).1 hv r hr
    exact inner_spec hk (csX_eq_csK h1 h2 hb _) rfl (hcv.2 t ht) (hcs.2 r hr) hr'

@[expose] noncomputable def rankK (i TB DB : ℕ) : Bool :=
  let pts := rankPts i
  (List.range 5).all fun m => (List.range 5).all fun j =>
    bX (pts.2.getD m 0) ((fun x => x ^^^ kapL TB DB x) (pts.1.getD j 0)) == decide (m = j)

theorem rankOKT_of {i TB DB : ℕ} (h1 : PermArr (cosetArr i) = true) (h2 : AutArr (cosetArr i))
    (hb : BasisOK i TB DB) (hr : rankK i TB DB = true) : rankOKT (tT i) (tD i) i = true := by
  have hMX : MX (tT i) (tD i) = fun x => x ^^^ kapL TB DB x := by
    funext x
    unfold MX
    rw [kapX_eq_kapL h1 h2 hb]
  unfold rankOKT
  rw [hMX]
  unfold rankK at hr
  exact hr

end CertificateChecks.MonsterExist.ELevel

end

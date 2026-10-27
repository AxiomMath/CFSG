module

public import Certificates.Kernel.ONOut.Out2
public import Certificates.Kernel.ONOut.Checks1
public import Certificates.Kernel.ONOut.Light1
public import Certificates.Kernel.VecCert.WordProg
public import Certificates.Kernel.VecCert.HomBound3
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

set_option maxRecDepth 400000

namespace CFSG.KD.ONOut

#kc_forall_chunks IV.all (fun g => ivC g = true) 8 CFSG.KD.ONOut.ivC 1
#kc_forall_chunks S.all (fun k => sC k = true) 16 CFSG.KD.ONOut.sC 1

end CFSG.KD.ONOut

namespace CertificateChecks.KernelONOut

open CFSG.KC.Ord CFSG.KC.ONOut CFSG.KS.Mat3 CFSG.KS.ONOut CFSG.KD.ONOut CFSG.F3.Native
  CFSG.ComponentClassification.SolMax.ONOut CFSG.Sporadic.ON.Native CFSG.KC.WP
  CertificateChecks.KernelWP CertificateChecks.KernelHomG CertificateChecks.KernelHom3

local notation "Mt" => mat3 154 23716

theorem hs : LayoutSound (Canon3 23716) Mt MUL VLD ONE := layout3 consts

theorem recAnd1 {f : Nat → Bool} : ∀ n, (∀ g < n, f g = true) →
    Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) n = true
  | 0, _ => rfl
  | n + 1, h => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih (f g)) n) (f n) = true
    rw [recAnd1 n (fun g hg => h g (by omega)), h n (by omega)]
    rfl

theorem iv_at : ∀ g < 8, andB (VLD (RB (Nat.add (Nat.succ 8) g)))
    (Nat.beq (MUL (RB (Nat.succ g)) (RB (Nat.add (Nat.succ 8) g))) ONE) = true :=
  CFSG.KD.ONOut.IV.all

theorem invsOK_of' {RB' : Nat → Nat} {mul : Nat → Nat → Nat} {vld : Nat → Bool} {L ONE' : Nat}
    (h : ∀ g < L, andB (vld (RB' (Nat.add (Nat.succ L) g)))
      (Nat.beq (mul (RB' (Nat.succ g)) (RB' (Nat.add (Nat.succ L) g))) ONE') = true) :
    invsOK RB' mul vld L ONE' = true :=
  recAnd1 L h

theorem hinv : invsOK RB MUL VLD 8 ONE = true := invsOK_of' iv_at

theorem hroot : rootsOK RB VLD 1 (8 + 1) = true := hroots

theorem good : ∀ k < 16, Good (Canon3 23716) Mt RB 8 (RS k) (WC k) := by
  exact states_good hs hroot hinv statesL CFSG.KD.ONOut.S.all

theorem letM_pos (m : ℕ) : letM RB 8 (letC (2 * m + 1)) = RB (m + 1) := by
  rw [letC_div, show (2 * m + 1) / 2 = m by omega,
    decide_eq_true (show (2 * m + 1) % 2 = 1 by omega)]
  rfl

theorem letM_neg (m : ℕ) : letM RB 8 (letC (2 * m)) = RB (9 + m) := by
  rw [letC_div, show 2 * m / 2 = m by omega,
    decide_eq_false (show ¬ (2 * m) % 2 = 1 by omega)]
  change RB (Nat.add (Nat.succ 8) m) = RB (9 + m)
  rfl

theorem canon_reg (m : ℕ) (hm : m < 8) : Canon3 23716 (RB (m + 1)) ∧ Canon3 23716 (RB (9 + m)) := by
  have h1 := (good_let hs hroot hinv (c := 2 * m + 1) (by omega)).1
  have h2 := (good_let hs hroot hinv (c := 2 * m) (by omega)).1
  rw [letM_pos] at h1
  rw [letM_neg] at h2
  exact ⟨h1, h2⟩

theorem inv_at (m : ℕ) (hm : m < 8) : Mt (RB (m + 1)) * Mt (RB (9 + m)) = 1 := by
  obtain ⟨-, h2⟩ := andB_true3 (iv_at m hm)
  have e : MUL (RB (m + 1)) (RB (9 + m)) = ONE := Nat.eq_of_beq_eq_true h2
  rw [← (hs.mul_sound _ _ (canon_reg m hm).1 (canon_reg m hm).2).2, e, hs.one_mt]

@[expose] def code (l : Int) : ℕ := if 0 < l then 2 * (l.toNat - 1) + 1 else 2 * ((-l).toNat - 1)

@[expose] def GoodArr (S Si : Array (Array V)) (n : ℕ) : Prop :=
  S.size = n ∧ Si.size = n ∧ ∀ i < n, canonM 154 S[i]! = true ∧ toMat 154 S[i]! = Mt (RB (i + 1)) ∧
    canonM 154 Si[i]! = true ∧ toMat 154 Si[i]! = Mt (RB (9 + i))

theorem goodArr_nil : GoodArr #[] #[] 0 := ⟨rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem getElem!_push_lt' {a : Array (Array V)} {x : Array V} {i : ℕ} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt h]

theorem getElem!_push_eq' (a : Array (Array V)) (x : Array V) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos _ _ (by simp)]
  simp

theorem goodArr_push {S Si : Array (Array V)} {n : ℕ} (h : GoodArr S Si n) {X : Array V}
    (hX : canonM 154 X = true) (hm : toMat 154 X = Mt (RB (n + 1))) (hn : n < 8) :
    GoodArr (S.push X) (Si.push (invV 154 X)) (n + 1) := by
  obtain ⟨hS, hSi, hi⟩ := h
  obtain ⟨i1, i2⟩ := invV_sound hX (by rw [hm]; exact inv_at n hn)
  refine ⟨by simp [hS], by simp [hSi], fun i hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | e
  · rw [getElem!_push_lt' (by omega), getElem!_push_lt' (by omega)]
    exact hi i hi'
  · have hx : (S.push X)[i]! = X := by rw [show i = S.size by omega, getElem!_push_eq']
    have hy : (Si.push (invV 154 X))[i]! = invV 154 X := by
      rw [show i = Si.size by omega, getElem!_push_eq']
    rw [hx, hy, e]
    exact ⟨hX, hm, i1, i2⟩

theorem letter_ok {S Si : Array (Array V)} {n : ℕ} (h : GoodArr S Si n) (l : Int) (hl0 : l ≠ 0)
    (hl : l.natAbs ≤ n) : canonM 154 (letterRows S Si l) = true ∧
      toMat 154 (letterRows S Si l) = Mt (letM RB 8 (letC (code l))) := by
  obtain ⟨-, -, hi⟩ := h
  unfold letterRows code
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp, letM_pos]
    have hm : l.toNat - 1 < n := by omega
    exact ⟨(hi _ hm).1, by rw [(hi _ hm).2.1, Nat.sub_add_cancel (by omega)]⟩
  · rw [if_neg hp, if_neg hp, letM_neg]
    have hm : (-l).toNat - 1 < n := by omega
    exact ⟨(hi _ hm).2.2.1, (hi _ hm).2.2.2⟩

theorem word_ok {S Si : Array (Array V)} {n : ℕ} (h : GoodArr S Si n) (w : List Int)
    (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ n) : canonM 154 (wordRows S Si w) = true ∧
      toMat 154 (wordRows S Si w) = wordMat Mt RB 8 (w.map code) := by
  obtain ⟨h1, h2⟩ := wordRows_spec S Si w fun l hl => (letter_ok h l (hw l hl).1 (hw l hl).2).1
  refine ⟨h1, ?_⟩
  rw [h2]
  unfold wordMat
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  exact (letter_ok h l (hw l hl).1 (hw l hl).2).2

theorem good_mat {k : ℕ} (hk : k < 16) : Mt (RS k) = wordMat Mt RB 8 (WC k) := (good k hk).2

theorem rb1 : RB 1 = MT 0 := rfl
theorem rb2 : RB 2 = MT 1 := rfl
theorem rb8 : RB 8 = MT 2 := rfl

theorem w2 : (∀ l ∈ CFSG.ONSchreier.Data.strongWords[2]!, l ≠ 0 ∧ l.natAbs ≤ 2) ∧
    WC 11 = (CFSG.ONSchreier.Data.strongWords[2]!).map code := by decide
theorem w3 : (∀ l ∈ CFSG.ONSchreier.Data.strongWords[3]!, l ≠ 0 ∧ l.natAbs ≤ 3) ∧
    WC 12 = (CFSG.ONSchreier.Data.strongWords[3]!).map code := by decide
theorem w4 : (∀ l ∈ CFSG.ONSchreier.Data.strongWords[4]!, l ≠ 0 ∧ l.natAbs ≤ 4) ∧
    WC 13 = (CFSG.ONSchreier.Data.strongWords[4]!).map code := by decide
theorem w5 : (∀ l ∈ CFSG.ONSchreier.Data.strongWords[5]!, l ≠ 0 ∧ l.natAbs ≤ 5) ∧
    WC 14 = (CFSG.ONSchreier.Data.strongWords[5]!).map code := by decide
theorem w6 : (∀ l ∈ CFSG.ONSchreier.Data.strongWords[6]!, l ≠ 0 ∧ l.natAbs ≤ 6) ∧
    WC 15 = (CFSG.ONSchreier.Data.strongWords[6]!).map code := by decide

theorem strong_step {S Si : Array (Array V)} {j : ℕ} (h : GoodArr S Si j) (hj : j < 7) (hj9 : 9 + j < 16)
    (w : List Int) (hw : (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j) ∧ WC (9 + j) = w.map code)
    (hR : RS (9 + j) = RB (j + 1)) :
    GoodArr (S.push (wordRows S Si w)) (Si.push (invV 154 (wordRows S Si w))) (j + 1) := by
  obtain ⟨c1, c2⟩ := word_ok h w hw.1
  refine goodArr_push h c1 ?_ (by omega)
  rw [c2, ← hw.2, ← good_mat hj9, hR]

theorem g0 : GoodArr #[sR0] #[sI0] 1 := goodArr_push goodArr_nil cA mA (by norm_num)

theorem g1 : GoodArr #[sR0, sR1] #[sI0, sI1] 2 := goodArr_push g0 cB mB (by norm_num)

theorem g2 : GoodArr #[sR0, sR1, sR2] #[sI0, sI1, sI2] 3 :=
  strong_step g1 (by norm_num) (by norm_num) _ w2 rfl

theorem g3 : GoodArr #[sR0, sR1, sR2, sR3] #[sI0, sI1, sI2, sI3] 4 :=
  strong_step g2 (by norm_num) (by norm_num) _ w3 rfl

theorem g4 : GoodArr #[sR0, sR1, sR2, sR3, sR4] #[sI0, sI1, sI2, sI3, sI4] 5 :=
  strong_step g3 (by norm_num) (by norm_num) _ w4 rfl

theorem g5 : GoodArr #[sR0, sR1, sR2, sR3, sR4, sR5] #[sI0, sI1, sI2, sI3, sI4, sI5] 6 :=
  strong_step g4 (by norm_num) (by norm_num) _ w5 rfl

theorem g6 : GoodArr sRows sIRows 7 :=
  strong_step g5 (by norm_num) (by norm_num) _ w6 rfl

theorem n0Inv_facts : canonM 154 n0InvRows = true ∧ toMat 154 n0InvRows = Mt (RB 16) :=
  invV_sound cN (by rw [mN, ← rb8]; exact inv_at 7 (by norm_num))

theorem mul_facts {X Y : Array V} (hX : canonM 154 X = true) (hY : canonM 154 Y = true) :
    canonM 154 (mul 154 X Y) = true ∧ toMat 154 (mul 154 X Y) = toMat 154 X * toMat 154 Y :=
  ⟨canonM_mul (canonM_spec hX).1 (RowsWF.of_canonM hX) hY,
    toMat_mul (canonM_spec hX).1 (RowsWF.of_canonM hX) (RowsWF.of_canonM hY)⟩

theorem wordMat_three (a b c : ℕ) : wordMat Mt RB 8 [a, b, c] =
    Mt (letM RB 8 (letC a)) * Mt (letM RB 8 (letC b)) * Mt (letM RB 8 (letC c)) := by
  unfold wordMat
  simp [mul_assoc]

theorem wordMat_cons' (c : ℕ) (w : List ℕ) :
    wordMat Mt RB 8 (c :: w) = Mt (letM RB 8 (letC c)) * wordMat Mt RB 8 w := by
  unfold wordMat
  rw [List.map_cons, List.prod_cons]

theorem wordMat_snoc (w : List ℕ) (c : ℕ) :
    wordMat Mt RB 8 (w ++ [c]) = wordMat Mt RB 8 w * Mt (letM RB 8 (letC c)) := by
  rw [wordMat_append]
  unfold wordMat
  simp

theorem l15 : letM RB 8 (letC 15) = RB 8 := letM_pos 7
theorem l14 : letM RB 8 (letC 14) = RB 16 := letM_neg 7
theorem l1 : letM RB 8 (letC 1) = RB 1 := letM_pos 0
theorem l3 : letM RB 8 (letC 3) = RB 2 := letM_pos 1

theorem n0_check : (okRows n0Rows && okRows n0InvRows &&
    eqM 154 (mul 154 n0Rows n0InvRows) (idM 154)) = true := by
  obtain ⟨i1, i2⟩ := n0Inv_facts
  obtain ⟨m1, m2⟩ := mul_facts cN i1
  have he : eqM 154 (mul 154 n0Rows n0InvRows) (idM 154) = true := by
    refine eqM_of_toMat m1 (canonM_idM 154) ?_
    rw [m2, mN, i2, ← rb8, inv_at 7 (by norm_num), toMat_idM]
  rw [okRows_of cN, okRows_of i1, he]
  rfl

theorem strong_check : ((List.range 7).all fun j =>
    okRows sIRows[j]! && eqM 154 (mul 154 sRows[j]! sIRows[j]!) (idM 154)) = true := by
  obtain ⟨-, -, hg⟩ := g6
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  obtain ⟨a1, a2, a3, a4⟩ := hg j hj'
  obtain ⟨m1, m2⟩ := mul_facts a1 a3
  have he : eqM 154 (mul 154 sRows[j]! sIRows[j]!) (idM 154) = true := by
    refine eqM_of_toMat m1 (canonM_idM 154) ?_
    rw [m2, a2, a4, inv_at j (by omega), toMat_idM]
  rw [okRows_of a3, he]
  rfl

theorem wA_ok : (∀ l ∈ wA, l ≠ 0 ∧ l.natAbs ≤ 7) ∧ WC 2 = wA.map code ∧ WC 1 = [15, 1, 14] := by
  decide
theorem wB_ok : (∀ l ∈ wB, l ≠ 0 ∧ l.natAbs ≤ 7) ∧ WC 4 = wB.map code ∧ WC 3 = [15, 3, 14] := by
  decide
theorem z_ok : (∀ l ∈ CFSG.ONSchreier.Data.zWord, l ≠ 0 ∧ l.natAbs ≤ 7) ∧
    WC 0 = CFSG.ONSchreier.Data.zWord.map code ∧ WC 5 = 15 :: WC 0 ∧ WC 6 = WC 0 ++ [15] := by
  decide
theorem sq_ok : WC 7 = [15, 15, 1] ∧ WC 8 = [1, 15, 15] ∧ WC 9 = [15, 15, 3] ∧
    WC 10 = [3, 15, 15] := by decide

theorem conj_of {G : Array V} {w : List Int} {k k' : ℕ} {c : ℕ} (hk : k < 16) (hk' : k' < 16)
    (hG : canonM 154 G = true) (hGm : toMat 154 G = Mt (letM RB 8 (letC c)))
    (hw : (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 7) ∧ WC k' = w.map code ∧ WC k = [15, c, 14])
    (hRS : RS k = RS k') :
    eqM 154 (mul 154 (mul 154 n0Rows G) n0InvRows) (wordRows sRows sIRows w) = true := by
  obtain ⟨i1, i2⟩ := n0Inv_facts
  obtain ⟨m1, m2⟩ := mul_facts cN hG
  obtain ⟨p1, p2⟩ := mul_facts m1 i1
  obtain ⟨w1, w2⟩ := word_ok g6 w hw.1
  refine eqM_of_toMat p1 w1 ?_
  rw [p2, m2, mN, hGm, i2, w2, ← hw.2.1, ← good_mat hk', ← hRS, good_mat hk, hw.2.2, wordMat_three,
    l15, l14, rb8]

theorem conjA_check :
    eqM 154 (mul 154 (mul 154 n0Rows rowsA) n0InvRows) (wordRows sRows sIRows wA) = true :=
  conj_of (k := 1) (k' := 2) (by norm_num) (by norm_num) cA (by rw [mA, l1, rb1]) wA_ok rfl

theorem conjB_check :
    eqM 154 (mul 154 (mul 154 n0Rows rowsB) n0InvRows) (wordRows sRows sIRows wB) = true :=
  conj_of (k := 3) (k' := 4) (by norm_num) (by norm_num) cB (by rw [mB, l3, rb2]) wB_ok rfl

theorem z_check : eqM 154 (mul 154 n0Rows zRows) (mul 154 zRows n0Rows) = true := by
  obtain ⟨z1, z2⟩ := word_ok g6 CFSG.ONSchreier.Data.zWord z_ok.1
  have hz : toMat 154 zRows = Mt (RS 0) := by
    unfold zRows
    rw [z2, ← z_ok.2.1, ← good_mat (by norm_num)]
  have cz : canonM 154 zRows = true := z1
  obtain ⟨m1, m2⟩ := mul_facts cN cz
  obtain ⟨p1, p2⟩ := mul_facts cz cN
  refine eqM_of_toMat m1 p1 ?_
  have e : RS 5 = RS 6 := rfl
  have h5 := good_mat (k := 5) (by norm_num)
  have h6 := good_mat (k := 6) (by norm_num)
  rw [z_ok.2.2.1, wordMat_cons', ← good_mat (k := 0) (by norm_num), l15] at h5
  rw [z_ok.2.2.2, wordMat_snoc, ← good_mat (k := 0) (by norm_num), l15] at h6
  rw [m2, p2, hz, mN, ← rb8, ← h5, e, h6]

theorem sq_pair {G : Array V} {c k k' : ℕ} (hk : k < 16) (hk' : k' < 16) (hG : canonM 154 G = true)
    (hGm : toMat 154 G = Mt (letM RB 8 (letC c))) (h1 : WC k = [15, 15, c]) (h2 : WC k' = [c, 15, 15])
    (hRS : RS k = RS k') :
    eqM 154 (mul 154 n0SqRows G) (mul 154 G n0SqRows) = true := by
  obtain ⟨q1, q2⟩ := mul_facts cN cN
  have cq : canonM 154 n0SqRows = true := q1
  obtain ⟨m1, m2⟩ := mul_facts cq hG
  obtain ⟨p1, p2⟩ := mul_facts hG cq
  refine eqM_of_toMat m1 p1 ?_
  have ha := good_mat hk
  have hb := good_mat hk'
  rw [h1, wordMat_three, l15] at ha
  rw [h2, wordMat_three, l15] at hb
  have hsq : toMat 154 n0SqRows = Mt (RB 8) * Mt (RB 8) := by
    change toMat 154 (mul 154 n0Rows n0Rows) = _
    rw [q2, mN, rb8]
  rw [m2, p2, hsq, hGm, ← ha, hRS, hb, mul_assoc]

theorem sq_check : (eqM 154 (mul 154 n0SqRows rowsA) (mul 154 rowsA n0SqRows) &&
    eqM 154 (mul 154 n0SqRows rowsB) (mul 154 rowsB n0SqRows)) = true := by
  rw [sq_pair (k := 7) (k' := 8) (by norm_num) (by norm_num) cA (by rw [mA, l1, rb1]) sq_ok.1
      sq_ok.2.1 rfl,
    sq_pair (k := 9) (k' := 10) (by norm_num) (by norm_num) cB (by rw [mB, l3, rb2]) sq_ok.2.2.1
      sq_ok.2.2.2 rfl]
  rfl

theorem facts22231 :
    (okRows n0Rows && okRows n0InvRows && eqM 154 (mul 154 n0Rows n0InvRows) (idM 154)) = true ∧
    ((List.range 7).all fun j =>
      okRows sIRows[j]! && eqM 154 (mul 154 sRows[j]! sIRows[j]!) (idM 154)) = true ∧
    eqM 154 (mul 154 (mul 154 n0Rows rowsA) n0InvRows) (wordRows sRows sIRows wA) = true ∧
    eqM 154 (mul 154 (mul 154 n0Rows rowsB) n0InvRows) (wordRows sRows sIRows wB) = true ∧
    eqM 154 (mul 154 n0Rows zRows) (mul 154 zRows n0Rows) = true ∧
    (eqM 154 (mul 154 n0SqRows rowsA) (mul 154 rowsA n0SqRows) &&
      eqM 154 (mul 154 n0SqRows rowsB) (mul 154 rowsB n0SqRows)) = true :=
  ⟨n0_check, strong_check, conjA_check, conjB_check, z_check, sq_check⟩

end CertificateChecks.KernelONOut

end

module

public import Certificates.Kernel.J4NP7850.Checks
public import Certificates.Kernel.J4NP7850.SoundBase
public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.Kernel.J4NP7850.Spec
public import CFSG.Quasithin.Vol2.KGFactC31J4M4KW3

public section

namespace CertificateChecks.KernelJ4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4M4F CFSG.KD.J4NP7850 CFSG.KS.J4NP7850
  CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31.J4M4
  CertificateChecks.KernelJ4Q Matrix

theorem vecJ_vec {M : Array V2} (hM : WfA M) {x : Nat} (hx : x < 2 ^ 112) :
    vecJ rm x (encR M) < 2 ^ 112 ∧
      (ofN (vecJ rm x (encR M))).toVec = (ofN x).toVec ᵥ* rowsMatrix M := by
  have e := v2N_frApply hK hM (wf_ofN hx)
  rw [ofN_eq hx] at e
  have hlt : vecJ rm x (encR M) < 2 ^ 112 := e ▸ v2N_lt112 (wf_frApply hM (ofN x))
  refine ⟨hlt, ?_⟩
  have e2 : ofN (vecJ rm x (encR M)) = frApply (frTable M) (ofN x) :=
    VOrbBFS.v2N_inj (by rw [ofN_eq hlt, e])
  rw [e2, frApply_toVec_eq_vecMul]

theorem rowN_inj {x y : Nat} (hx : x < 2 ^ 112) (hy : y < 2 ^ 112) (h : rowN x = rowN y) :
    x = y := by
  have e : (ofN x).toVec = (ofN y).toVec := congrArg ofRow h
  have e2 := (V2.toVec_inj (wf_ofN hx) (wf_ofN hy)).1 e
  rw [← ofN_eq hx, ← ofN_eq hy, e2]

theorem rowN_v2N {v : V2} (hv : v2N v < 2 ^ 112) : rowN (v2N v) = toRow v.toVec := by
  unfold rowN
  rw [VOrbBFS.v2N_inj (ofN_eq hv)]

theorem inv_smul_rowN {g : J} {M : Array V2} (hMg : Mx g = rowsMatrix M) (hM : WfA M) {x : Nat}
    (hx : x < 2 ^ 112) : g⁻¹ • rowN x = rowN (vecJ rm x (encR M)) := by
  apply ofRow_inj.mp
  rw [inv_smul_row, ← Mx_apply, hMg]
  exact (vecJ_vec hM hx).2.symm

theorem kw_getD (k : Nat) : KW7850.getD k 0 = v2N (kwVecs.getD k V2.zero) :=
  CertificateChecks.KernelJ4M4F.getD_map_v2N kwVecs k

theorem G7850_enc : WfA (wordRows baseMats baseInvs gWord) ∧
    encR (wordRows baseMats baseInvs gWord) = G7850 :=
  enc_wordRows hK base_gens base_invs gWord

theorem pi_sound (hM : MatFacts) :
    ∀ k < 31, pv.getD k 0 < 2 ^ 112 ∧ KW7850.getD k 0 < 2 ^ 112 ∧
      rowN (pv.getD k 0) = gJ • kwRow k := by
  intro k hk
  obtain ⟨hlt, he⟩ := piK_spec c7850_pi k hk
  have hg := G7850_enc
  have h1 := inv_smul_rowN (g := gJ) (Mx_wordProd_baseJ hM gWord) hg.1 hlt
  have h2 := (vecJ_vec hg.1 hlt).1
  rw [hg.2, he] at h1 h2
  refine ⟨hlt, h2, ?_⟩
  rw [kw_getD] at h1 h2
  rw [rowN_v2N h2] at h1
  exact inv_smul_eq_iff.mp h1

@[expose] noncomputable def etaVn (Us : List Nat) (c0 v n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (vecJ rm acc (getN 0 Us j))
      (Nat.beq (Nat.land (Nat.shiftRight c0 j) 1) 1)) n

theorem Us_getN {j : Nat} (hj : j < 11) : getN 0 Us7850 j = getN one Us j := by
  rw [getN_eq, getN_eq, List.getD_eq_getElem _ _ (by rw [Us7850]; simpa using hj),
    List.getD_eq_getElem _ _ (by rw [Us_length]; exact hj)]
  rfl

theorem etaVn_spec (hM : MatFacts) (c0 : Nat) {x : Nat}
    (hx : x < 2 ^ 112) : ∀ n ≤ 11, etaVn Us7850 c0 x n < 2 ^ 112 ∧
      (ofN (etaVn Us7850 c0 x n)).toVec = (ofN x).toVec ᵥ* Mx (eta uJ n c0)
  | 0, _ => by
    refine ⟨hx, ?_⟩
    have e : eta uJ 0 c0 = 1 := rfl
    rw [e, map_one, Matrix.vecMul_one]
    rfl
  | n + 1, hn => by
    obtain ⟨ih1, ih2⟩ := etaVn_spec hM c0 hx n (by omega)
    change Bool.rec (motive := fun _ => Nat) (etaVn Us7850 c0 x n)
      (vecJ rm (etaVn Us7850 c0 x n) (getN 0 Us7850 n))
      (Nat.beq (Nat.land (Nat.shiftRight c0 n) 1) 1) < 2 ^ 112 ∧
      (ofN (Bool.rec (motive := fun _ => Nat) (etaVn Us7850 c0 x n)
        (vecJ rm (etaVn Us7850 c0 x n) (getN 0 Us7850 n))
        (Nat.beq (Nat.land (Nat.shiftRight c0 n) 1) 1))).toVec = _
    rw [land_shiftRight_one, eta_succ, map_mul]
    cases hb : c0.testBit n
    · refine ⟨ih1, ?_⟩
      simp only [Bool.false_eq_true, if_false, map_one, Matrix.mul_one]
      exact ih2
    · simp only [if_true]
      obtain ⟨hw, he⟩ := uTab_enc n (by rw [Us_length]; omega)
      rw [Us_getN (by omega), ← he]
      obtain ⟨v1, v2⟩ := vecJ_vec hw ih1
      refine ⟨v1, ?_⟩
      rw [v2, ih2, Matrix.vecMul_vecMul, Mx_uJ hM (by omega)]

theorem etaV_sound (hM : MatFacts) (c0 : Nat) {x : Nat}
    (hx : x < 2 ^ 112) :
    etaV rm Us7850 c0 x < 2 ^ 112 ∧ rowN (etaV rm Us7850 c0 x) = eta uJ 11 c0 • rowN x := by
  obtain ⟨h1, h2⟩ := etaVn_spec hM c0 hx 11 le_rfl
  refine ⟨h1, ?_⟩
  apply ofRow_inj.mp
  rw [smul_row, CFSG.Quasithin.J4Loc.eta_inv hM, ← Mx_apply]
  exact h2

theorem FM_getD {j : Nat} (hj : j < 10) :
    FM7850.getD j one = getN one CertificateChecks.KernelJ4M4F.FMs j := by
  rw [getN_eq]
  rfl

theorem kwFix_sound (hM : MatFacts) :
    ∀ j < 10, ∀ k < 31, fJn j • kwRow k = kwRow k := by
  intro j hj k hk
  have h := kwFixK_spec c7850_kwFix j hj k hk
  obtain ⟨-, hlt, -⟩ := pi_sound hM k hk
  obtain ⟨hw, he⟩ := CertificateChecks.KernelJ4M4F.fTab_enc j hj
  rw [FM_getD hj, ← he] at h
  have h1 := inv_smul_rowN (g := fJn j) (Mx_fJn hM hj) hw hlt
  rw [h, kw_getD, rowN_v2N (by rw [← kw_getD]; exact hlt)] at h1
  exact (inv_smul_eq_iff.mp h1).symm

theorem move_sound (hM : MatFacts) :
    ∃ k < 31, ∀ k' < 31, eta uJ 11 4 • (gJ • kwRow k) ≠ gJ • kwRow k' := by
  obtain ⟨hk, hne⟩ := moveK_spec c7850_move
  refine ⟨k4, hk, fun k' hk' e => ?_⟩
  obtain ⟨p1, -, p2⟩ := pi_sound hM k4 hk
  obtain ⟨q1, -, q2⟩ := pi_sound hM k' hk'
  obtain ⟨e1, e2⟩ := etaV_sound hM 4 p1
  rw [← p2, ← q2, ← e2] at e
  exact hne k' hk' (rowN_inj e1 q1 e)

theorem combK_zero (B : List Nat) : ∀ n, combK B n 0 = 0
  | 0 => rfl
  | n + 1 => by
    rw [combK_succ, Nat.zero_testBit]
    exact combK_zero B n

theorem mod_two_pow_succ_xor (c n : Nat) :
    c % 2 ^ (n + 1) = c % 2 ^ n ^^^ (if c.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  rcases Nat.lt_trichotomy i n with h | rfl | h
  · have h1 : i < n + 1 := by omega
    split <;> simp [h, h1, Nat.testBit_two_pow, Nat.ne_of_gt h]
  · split <;> simp_all [Nat.testBit_two_pow]
  · have h1 : ¬ i < n + 1 := by omega
    have h2 : ¬ i < n := by omega
    split <;> simp [h1, h2, Nat.testBit_two_pow, Nat.ne_of_lt h]

theorem xor_rearr (a b e p : Nat) : (a ^^^ b) ^^^ e = (a ^^^ (e ^^^ p)) ^^^ (b ^^^ p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases e.testBit i <;> cases p.testBit i <;> rfl

theorem y8_dec : ∀ n ≤ 11, ∀ c, ∃ s < 2 ^ 6, ∃ t < 2 ^ 5,
    c % 2 ^ n = combK y8Bk 6 s ^^^ combK cBk 5 t := by
  obtain ⟨-, hd2, hd3⟩ := y8DecK_spec c7850_y8dec
  intro n
  induction n with
  | zero =>
    intro _ c
    refine ⟨0, by norm_num, 0, by norm_num, ?_⟩
    rw [combK_zero, combK_zero, Nat.pow_zero, Nat.mod_one]
    rfl
  | succ n ih =>
    intro hn c
    obtain ⟨s, hs, t, ht, e⟩ := ih (by omega) c
    rw [mod_two_pow_succ_xor, e]
    cases hb : c.testBit n
    · exact ⟨s, hs, t, ht, by simp⟩
    · obtain ⟨⟨t', ht', et'⟩, hm⟩ := hd3 n (by omega)
      obtain ⟨s', hs', es'⟩ := hd2 _ hm
      obtain ⟨s2, hs2, es2⟩ := combK_xor_mem ⟨s, hs, rfl⟩ ⟨s', hs', rfl⟩
      obtain ⟨t2, ht2, et2⟩ := combK_xor_mem ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
      refine ⟨s2, hs2, t2, ht2, ?_⟩
      rw [if_pos rfl, es2, et2, es', et']
      exact xor_rearr _ _ _ _

@[expose] def Fx (c : Nat) : Prop := ∀ k < 31, eta uJ 11 c • rowN (pv.getD k 0) = rowN (pv.getD k 0)

theorem Fx_xor (hM : MatFacts) {a b : Nat} (ha : Fx a)
    (hb : Fx b) : Fx (a ^^^ b) := by
  intro k hk
  rw [← CFSG.Quasithin.J4Loc.eta_mul_eta hM, mul_smul, hb k hk, ha k hk]

theorem Fx_comb (hM : MatFacts) :
    ∀ n ≤ 6, ∀ s, Fx (combK y8Bk n s) := by
  intro n
  induction n with
  | zero =>
    intro _ s k _
    have e : combK y8Bk 0 s = 0 := rfl
    rw [e, eta_zero, one_smul]
  | succ n ih =>
    intro hn s
    rw [combK_succ]
    split
    · refine Fx_xor hM (ih (by omega) s) fun k hk => ?_
      obtain ⟨p1, -, -⟩ := pi_sound hM k hk
      obtain ⟨-, e2⟩ := etaV_sound hM (y8Bk.getD n 0) p1
      rw [← e2, y8FixK_spec c7850_y8fix n (by omega) k hk]
    · exact ih (by omega) s

theorem y8_sound (hM : MatFacts) :
    ∀ c < 2048, (∀ k < 31, eta uJ 11 c • (gJ • kwRow k) = gJ • kwRow k) ↔ c ∈ y8Lk := by
  intro c hc
  have hP : (∀ k < 31, eta uJ 11 c • (gJ • kwRow k) = gJ • kwRow k) ↔ Fx c :=
    forall₂_congr fun k hk => by rw [(pi_sound hM k hk).2.2]
  rw [hP]
  obtain ⟨hd1, hd2, -⟩ := y8DecK_spec c7850_y8dec
  constructor
  · intro hfx
    obtain ⟨s, hs, t, ht, e⟩ := y8_dec 11 le_rfl c
    rw [Nat.mod_eq_of_lt (by norm_num; exact hc)] at e
    have hl := Fx_comb hM 6 le_rfl s
    have hp : Fx (combK cBk 5 t) := by
      have e2 : c ^^^ combK y8Bk 6 s = combK cBk 5 t := by
        rw [e, Nat.xor_comm (combK y8Bk 6 s), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [← e2]
      exact Fx_xor hM hfx hl
    rcases t with _ | t
    · rw [e, combK_zero, Nat.xor_zero]
      exact hd1 s (by simpa using hs)
    · exfalso
      obtain ⟨hm, hne⟩ := y8MoveK_spec c7850_y8move t (by simp at ht; omega)
      obtain ⟨p1, -, -⟩ := pi_sound hM _ hm
      obtain ⟨e1, e2⟩ := etaV_sound hM (combK cBk 5 (t + 1)) p1
      exact hne (rowN_inj e1 p1 (by rw [e2]; exact hp _ hm))
  · intro hy
    obtain ⟨s, -, rfl⟩ := hd2 c hy
    exact Fx_comb hM 6 le_rfl s

end CertificateChecks.KernelJ4NP7850

end

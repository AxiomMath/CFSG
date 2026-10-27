module

public import CFSG.Monster.B.CTIB.VisibleOctadInputs
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public import CFSG.Certificates.Kernel.Common.XorBits

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.OctFix

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Rep4371
  CFSG.Monster.Visible CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.B.CTIB CFSG.KC.XorBits
  CFSG.Monster.Lifts

theorem cosetArr_perm : PermArr (cosetArr 1) = true := by decide +kernel

theorem cosetArr_aut : AutArr (cosetArr 1) := by decide +kernel

@[expose] noncomputable def pA : AutPerm :=
  ⟨decode (cosetArr 1), mem_AutPerm_of_arr cosetArr_perm cosetArr_aut⟩

theorem rep_pA : RepPerm (pA : Equiv.Perm (Fin 24)) (cosetArr 1) :=
  fun i => decode_apply cosetArr_perm i

@[expose] noncomputable def phi : Q ≃* Q :=
  (conjQ ⟨(YU ⟨toC (cosetA 1), 0⟩, gO (toC (cosetA 1))), YU_gO_mem_Pvis _⟩).trans
    (conjQ ⟨(sU pA, PO pA), sU_PO_mem_Pvis pA⟩)

theorem phi_pauliQ (y : Model.Pauli) : phi (pauliQ y) = pauliQ (alphaN 1 y) := by
  rw [phi, MulEquiv.trans_apply, conjQ_sign_toQ, conjQ_perm_toQ pA rep_pA, alphaN]

theorem phi_s (s : Bool) : phi (pauliQ (s, 0, 0)) = pauliQ (s, 0, 0) := by
  cases s
  · rw [pauliQ_false_zero, map_one]
  · rw [pauliQ_z, phi, MulEquiv.trans_apply, conjQ_zQ, conjQ_zQ]

attribute [local irreducible] alphaN

@[expose] def lo (n : ℕ) : ℕ := n % 2 ^ 12

@[expose] def hi (n : ℕ) : ℕ := n / 2 ^ 12 % 2 ^ 12

@[expose] def F (n : ℕ) : Model.Pauli :=
  Model.Pauli.mul (alphaN 1 (false, lo n, 0)) (alphaN 1 (false, 0, hi n))

@[expose] def pa (n : ℕ) : ℕ := (F n).2.1 % 2 ^ 12

@[expose] def pd (n : ℕ) : ℕ := (F n).2.2 % 2 ^ 12

@[expose] def fx (n : ℕ) : Prop := pa n = lo n ∧ pd n = hi n

instance (n : ℕ) : Decidable (fx n) := inferInstanceAs (Decidable (_ ∧ _))

attribute [local irreducible] lo hi

theorem lo_xor (a b : ℕ) : lo (a ^^^ b) = lo a ^^^ lo b := by
  rw [lo, lo, lo, Nat.xor_mod_two_pow]

theorem hi_xor (a b : ℕ) : hi (a ^^^ b) = hi a ^^^ hi b := by
  rw [hi, hi, hi, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

theorem parN_mod (x : ℕ) : Model.parN 12 (x % 2 ^ 12) = Model.parN 12 x :=
  boolZ_injective (by
    rw [boolZ_parN_eq_sum, boolZ_parN_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Nat.testBit_mod_two_pow, decide_eq_true i.2, Bool.true_and])

theorem pairN_mod (a d : ℕ) : Model.pairN (a % 2 ^ 12) (d % 2 ^ 12) = Model.pairN a d := by
  rw [Model.pairN, Model.pairN, ← Nat.and_mod_two_pow, parN_mod]

theorem pairN_zero (a : ℕ) : Model.pairN a 0 = false := by
  rw [Model.pairN, Nat.and_zero]
  rfl

theorem pairN_zero' (d : ℕ) : Model.pairN 0 d = false := by
  rw [Model.pairN, Nat.zero_and]
  rfl

@[expose] def red (x : Model.Pauli) : Model.Pauli := (x.1, x.2.1 % 2 ^ 12, x.2.2 % 2 ^ 12)

theorem pauliQ_red (x : Model.Pauli) : pauliQ (red x) = pauliQ x := by
  rcases x with ⟨s, a, d⟩
  rw [red, pauliQ_mod_d, pauliQ_mod_a]

theorem red_inj {x y : Model.Pauli} (h : pauliQ x = pauliQ y) : red x = red y :=
  pauliQ_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (by rw [pauliQ_red, pauliQ_red, h])

theorem mul_lo_hi (A D : ℕ) : Model.Pauli.mul (false, A, 0) (false, 0, D) = (false, A, D) := by
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero',
    Bool.xor_false, Nat.xor_zero, Nat.zero_xor]

theorem pauliQ_F (n : ℕ) : pauliQ (F n) = phi (pauliQ (false, lo n, hi n)) := by
  calc pauliQ (F n)
      = pauliQ (alphaN 1 (false, lo n, 0)) * pauliQ (alphaN 1 (false, 0, hi n)) := pauliQ_mul _ _
    _ = phi (pauliQ (false, lo n, 0)) * phi (pauliQ (false, 0, hi n)) :=
        congrArg₂ (· * ·) (phi_pauliQ _).symm (phi_pauliQ _).symm
    _ = phi (pauliQ (false, lo n, 0) * pauliQ (false, 0, hi n)) := (map_mul phi _ _).symm
    _ = phi (pauliQ (false, lo n, hi n)) :=
        congrArg phi ((pauliQ_mul _ _).symm.trans (congrArg pauliQ (mul_lo_hi _ _)))

theorem mul_codes (n m : ℕ) :
    Model.Pauli.mul (Model.pairN (lo m) (hi n), 0, 0)
        (Model.Pauli.mul (false, lo n, hi n) (false, lo m, hi m)) =
      (false, lo (n ^^^ m), hi (n ^^^ m)) := by
  rw [lo_xor, hi_xor]
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero,
    Bool.false_xor, Bool.xor_self, Nat.zero_xor]

theorem F_xor (n m : ℕ) : red (F (n ^^^ m)) =
    red (Model.Pauli.mul (Model.pairN (lo m) (hi n), 0, 0) (Model.Pauli.mul (F n) (F m))) := by
  refine red_inj ?_
  set c := Model.pairN (lo m) (hi n)
  calc pauliQ (F (n ^^^ m))
      = phi (pauliQ (false, lo (n ^^^ m), hi (n ^^^ m))) := pauliQ_F _
    _ = phi (pauliQ (c, 0, 0) * (pauliQ (false, lo n, hi n) * pauliQ (false, lo m, hi m))) :=
        congrArg phi ((congrArg pauliQ (mul_codes n m)).symm.trans
          ((pauliQ_mul _ _).trans (congrArg _ (pauliQ_mul _ _))))
    _ = phi (pauliQ (c, 0, 0)) * (phi (pauliQ (false, lo n, hi n)) *
          phi (pauliQ (false, lo m, hi m))) :=
        (map_mul phi _ _).trans (congrArg _ (map_mul phi _ _))
    _ = pauliQ (c, 0, 0) * (pauliQ (F n) * pauliQ (F m)) :=
        congrArg₂ (· * ·) (phi_s c) (congrArg₂ (· * ·) (pauliQ_F n).symm (pauliQ_F m).symm)
    _ = pauliQ (Model.Pauli.mul (c, 0, 0) (Model.Pauli.mul (F n) (F m))) :=
        (congrArg _ (pauliQ_mul _ _).symm).trans (pauliQ_mul _ _).symm

theorem pa_xor (n m : ℕ) : pa (n ^^^ m) = pa n ^^^ pa m := by
  have h := congrArg (fun x : Model.Pauli => x.2.1) (F_xor n m)
  simp only [red, Model.Pauli.mul, Model.Pauli.a, Nat.zero_xor] at h
  rw [pa, h, Nat.xor_mod_two_pow, pa, pa]

theorem pd_xor (n m : ℕ) : pd (n ^^^ m) = pd n ^^^ pd m := by
  have h := congrArg (fun x : Model.Pauli => x.2.2) (F_xor n m)
  simp only [red, Model.Pauli.mul, Model.Pauli.d, Nat.zero_xor] at h
  rw [pd, h, Nat.xor_mod_two_pow, pd, pd]

theorem s_xor (n m : ℕ) : (F (n ^^^ m)).1 =
    (Model.pairN (lo m) (hi n) ^^ ((F n).1 ^^ (F m).1 ^^ Model.pairN (F m).2.1 (F n).2.2)) := by
  have h := congrArg (fun x : Model.Pauli => x.1) (F_xor n m)
  simp only [red, Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d, pairN_zero,
    Bool.xor_false] at h
  exact h

theorem fx_xor {n m : ℕ} (hn : fx n) (hm : fx m) :
    fx (n ^^^ m) ∧ (F (n ^^^ m)).1 = ((F n).1 ^^ (F m).1) := by
  refine ⟨⟨by rw [pa_xor, lo_xor, hn.1, hm.1], by rw [pd_xor, hi_xor, hn.2, hm.2]⟩, ?_⟩
  rw [s_xor, ← pairN_mod (F m).2.1, ← pa, ← pd, hm.1, hn.2]
  cases Model.pairN (lo m) (hi n) <;> cases (F n).1 <;> cases (F m).1 <;> rfl

@[expose] def ga (n : ℕ) : ℕ := pa n ^^^ lo n

@[expose] def gd (n : ℕ) : ℕ := pd n ^^^ hi n

theorem ga_xor (a b : ℕ) : ga (a ^^^ b) = ga a ^^^ ga b := by
  rw [ga, ga, ga, pa_xor, lo_xor, xor_xor_xor]

theorem gd_xor (a b : ℕ) : gd (a ^^^ b) = gd a ^^^ gd b := by
  rw [gd, gd, gd, pd_xor, hi_xor, xor_xor_xor]

theorem fx_iff (n : ℕ) : fx n ↔ ga n = 0 ∧ gd n = 0 := by
  have e : ∀ a b : ℕ, a ^^^ b = 0 ↔ a = b := fun a b =>
    ⟨fun h => by rw [← Nat.xor_zero a, ← h, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor],
      fun h => by rw [h, Nat.xor_self]⟩
  rw [fx, ga, gd, e, e]

@[expose] def wRows : List ℕ :=
  [3, 12, 20, 36, 1024, 2048, 12288, 49152, 81920, 147456, 262144, 524288, 1048576, 2097152,
    4194304, 8388608, 1, 4, 64, 128, 256, 512, 4096, 16384]

@[expose] def wInvRows : List ℕ :=
  [65536, 65537, 131072, 131074, 131076, 131080, 262144, 524288, 1048576, 2097152, 16, 32, 4194304,
    4194368, 8388608, 8388736, 8388864, 8389120, 1024, 2048, 4096, 8192, 16384, 32768]

@[expose] def gaRows : List ℕ := [0, 63, 0, 0, 0, 0, 60, 3]

@[expose] def gdRows : List ℕ := [60, 3, 128, 64, 512, 256, 60, 60]

@[expose] def w (i : ℕ) : ℕ := wRows.getD i 0

@[expose] def wInv (i : ℕ) : ℕ := wInvRows.getD i 0

theorem w_inv : ∀ i < 24, xorB w (wInv i) 24 = 2 ^ i := by decide +kernel

theorem fx_zero : fx 0 ∧ (F 0).1 = false := by decide +kernel

theorem fx_w : ∀ j < 16, fx (w j) ∧ (F (w j)).1 = false := by decide +kernel

theorem g_w : ∀ j < 8, ga (w (16 + j)) = gaRows.getD j 0 ∧ gd (w (16 + j)) = gdRows.getD j 0 := by
  decide +kernel

theorem g_indep : ∀ m < 2 ^ 8, xorB (fun j => gaRows.getD j 0) m 8 = 0 →
    xorB (fun j => gdRows.getD j 0) m 8 = 0 → m = 0 := by decide +kernel

theorem fx_w16_ne : ¬ fx (w 16) := by decide +kernel

theorem g_indep_corrupt : ¬ ∀ m < 2 ^ 8, xorB (fun j => (0 :: gaRows.tail).getD j 0) m 8 = 0 →
    xorB (fun j => (0 :: gdRows.tail).getD j 0) m 8 = 0 → m = 0 := by decide +kernel

theorem span_fixed (c : ℕ) : ∀ k ≤ 16, fx (xorB w c k) ∧ (F (xorB w c k)).1 = false
  | 0, _ => fx_zero
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := span_fixed c k (by omega)
    rw [xorB_succ]
    by_cases hb : c.testBit k = true
    · rw [ite_eq_left hb]
      obtain ⟨h3, h4⟩ := fx_w k (by omega)
      obtain ⟨h5, h6⟩ := fx_xor h1 h3
      exact ⟨h5, by rw [h6, h2, h4]; rfl⟩
    · rw [ite_eq_right hb, Nat.xor_zero]
      exact ⟨h1, h2⟩

theorem decomp {n : ℕ} (hn : n < 2 ^ 24) : xorB w (xorB wInv n 24) 24 = n := by
  have h := xorB_hom (P := fun t => xorB w t 24) (fun a b => xorB_xor w a b 24) wInv n 24
  rw [h, xorB_congr_fun n 24 w_inv, xorB_two_pow hn]

theorem tail_zero (m : ℕ) (h : fx (xorB (fun j => w (16 + j)) m 8)) :
    xorB (fun j => w (16 + j)) m 8 = 0 := by
  obtain ⟨ha, hd⟩ := (fx_iff _).1 h
  have hga : xorB (fun j => gaRows.getD j 0) (m % 2 ^ 8) 8 = 0 := by
    rw [xorB_mod, ← xorB_congr_fun _ 8 fun j hj => (g_w j hj).1,
      ← xorB_hom (P := ga) ga_xor]
    exact ha
  have hgd : xorB (fun j => gdRows.getD j 0) (m % 2 ^ 8) 8 = 0 := by
    rw [xorB_mod, ← xorB_congr_fun _ 8 fun j hj => (g_w j hj).2,
      ← xorB_hom (P := gd) gd_xor]
    exact hd
  rw [← xorB_mod, g_indep _ (Nat.mod_lt _ (by norm_num)) hga hgd, xorB_zero]

theorem sign_of_fx {n : ℕ} (hn : n < 2 ^ 24) (h : fx n) : (F n).1 = false := by
  have e : n = xorB w (xorB wInv n 24) 16 ^^^
      xorB (fun j => w (16 + j)) (xorB wInv n 24 >>> 16) 8 := by
    rw [← xorB_add w _ 16 8]
    exact (decomp hn).symm
  generalize xorB wInv n 24 = c at e
  generalize hn1 : xorB w c 16 = n1 at e
  generalize hn' : xorB (fun j => w (16 + j)) (c >>> 16) 8 = n' at e
  obtain ⟨h1, h2⟩ := span_fixed c 16 le_rfl
  rw [hn1] at h1 h2
  have e' : n' = n1 ^^^ n := by rw [e, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hfx : fx n' := by
    rw [e']
    exact (fx_xor h1 h).1
  have h0 : n' = 0 := by
    rw [← hn'] at hfx ⊢
    exact tail_zero _ hfx
  rw [h0, Nat.xor_zero] at e
  rw [e]
  exact h2

theorem octFixTest_eq (n : ℕ) : octFixTest (tT 1) (tD 1) n =
    (!((pa n == lo n) && (pd n == hi n)) || !(F n).1) := by
  rw [octFixTest, native_mul_apply, tT_get 1 (Nat.mod_lt _ (by norm_num)),
    tD_get 1 (Nat.mod_lt _ (by norm_num))]
  simp only [pa, pd, F, lo, hi]

theorem octFixTest_true {n : ℕ} (hn : n < 2 ^ 24) : octFixTest (tT 1) (tD 1) n = true := by
  rw [octFixTest_eq]
  by_cases h : fx n
  · rw [sign_of_fx hn h, Bool.not_false, Bool.or_true]
  · have h' : ((pa n == lo n) && (pd n == hi n)) = false := by
      cases hb : ((pa n == lo n) && (pd n == hi n))
      · rfl
      · exact absurd (by simpa [fx, Bool.and_eq_true, beq_iff_eq] using hb) h
    rw [h', Bool.not_false, Bool.true_or]

theorem octFixCount_eq : octFixCount (tT 1) (tD 1) = 2 ^ 24 := by
  rw [octFixCount, CFSG.Monster.B.TwoA.Census.countBelow_eq, Nat.zero_add, Finset.filter_true_of_mem fun n hn =>
    octFixTest_true (Finset.mem_range.1 hn), Finset.card_range]

end CertificateChecks.OctFix

module

public import Certificates.Kernel.MonsterExist.ShortKey.Defs
public import CFSG.Certificates.Kernel.Trace6091.TwinEq
public import CFSG.Monster.AxisCount.DenseShort
public import CFSG.Monster.B.Rep4371.Raw
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.ShortKey

open CFSG.KC CFSG.KC.Loop CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster CFSG.Monster.B
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.B.Rep4371 CFSG.Monster.AxisCount

theorem popcN_sum : ∀ k a, Model.popcN k a = ∑ i ∈ Finset.range k, (a.testBit i).toNat
  | 0, _ => rfl
  | k + 1, a => by
    rw [Model.popcN, popcN_sum k (a / 2), Finset.sum_range_succ', Nat.testBit_zero]
    simp only [Nat.testBit_div_two]
    rw [Nat.add_comm]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]

theorem popcT_sum (a : ℕ) : ∀ k, popcT k a = ∑ i ∈ Finset.range k, (a.testBit i).toNat
  | 0 => rfl
  | k + 1 => by
    rw [Finset.sum_range_succ, ← popcT_sum a k, ← bitN_eq]
    rfl

theorem popcT_eq (k a : ℕ) : popcT k a = Model.popcN k a := by
  rw [popcT_sum, popcN_sum]

theorem selB_eq (b m : ℕ) (hb : b = 0 ∨ b = 1) : selB b m = if b = 1 then m else 0 := by
  rcases hb with rfl | rfl <;> simp [selB]

theorem bitN_le (x i : ℕ) : bitN x i = 0 ∨ bitN x i = 1 := by
  rw [bitN_eq]
  cases x.testBit i <;> simp

theorem du_ok : ∀ i < 24, fld(DU, Nat.mul (nat_lit 12) i, nat_lit 4095) = Model.dualN (2 ^ i) := by
  decide +kernel

theorem shl_one (i : ℕ) : Nat.shiftLeft (nat_lit 1) i = 2 ^ i := by
  change 1 <<< i = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem beq_true {a b : ℕ} : Nat.beq a b = true ↔ a = b := by simp

theorem blt_true {a b : ℕ} : Nat.blt a b = true ↔ a < b := by simp [Nat.blt_eq]

theorem bRec_true {c t e : Bool} :
    Bool.rec (motive := fun _ => Bool) e t c = true ↔ (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

theorem bAnd_true {a b : Bool} : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem nIf_eq (c : Bool) (t e : ℕ) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem coordOf_pauliQ' (y : Model.Pauli) : coordOf (pauliQ y) = (toC y.a, toD y.d) :=
  coordOf_spinEquiv _

theorem short_odd {a th wc pc d i : ℕ} (hth : th = Model.thetaN a) (hwc : wc = Model.wordN (cOf a))
    (hpc : pc = pK wc) (h : oddOK a th wc pc d i = true) : IsShortCoord (toC a, toD d) := by
  unfold oddOK at h
  simp only [bAnd_true, beq_true, blt_true] at h
  obtain ⟨hi, ha, hd⟩ := h
  set c := cOf a with hc
  have hc0 : c.testBit 0 = false := by
    rw [hc, cOf, nIf_eq]
    by_cases h0 : Nat.beq (Nat.land a (nat_lit 1)) (nat_lit 0) = true
    · simp only [h0, ↓reduceIte]
      have : a &&& 1 = 0 := beq_true.1 h0
      rw [Nat.testBit_zero]
      have h2 : a % 2 = 0 := by rw [← Nat.and_one_is_mod]; exact this
      simp [h2]
    · simp only [h0, Bool.false_eq_true, ↓reduceIte]
      have h1 : a &&& 1 ≠ 0 := fun e => h0 (beq_true.2 e)
      rw [Nat.and_one_is_mod] at h1
      have h2 : a % 2 = 1 := by omega
      change (a ^^^ 63).testBit 0 = false
      rw [Nat.testBit_xor, Nat.testBit_zero]
      simp [h2]
  have hpc' : pc = (Model.pN c).toNat := by
    rw [hpc, hwc, pK, popcT_eq]
    change (Model.popcN 24 (Model.wordN c) >>> 2) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    unfold Model.pN
    rcases Nat.mod_two_eq_zero_or_one (Model.popcN 24 (Model.wordN c) / 4) with h | h <;> simp [h]
  have hoc : Model.oddCode c i = a := by
    rw [← ha, hpc', hwc, bitN_eq]
    change _ = c ^^^ selB (((Model.wordN c).testBit i).toNat ^^^ (Model.pN c).toNat) 63
    rw [← toNat_xor, selB_toNat]
    unfold Model.oddCode
    rfl
  have hd' : d = Model.thetaN a ^^^ Model.dualN (2 ^ i) := by
    rw [hd, hth, du_ok i hi]
    rfl
  have h := isShortCoord_labelElt (.inr (.inr (.inl (π₀ (toC c), ⟨i, hi⟩))) : ShortLabel)
  have e := pauliQ_odd' c hc0 ⟨i, hi⟩
  simp only [labelElt] at h
  rw [← e, coordOf_pauliQ'] at h
  rw [hoc] at h
  rw [hd']
  exact h

@[expose] def wSet (δ : ℕ) : Finset (Fin 24) := Finset.univ.filter fun i => δ.testBit i

theorem ind_wSet (δ : ℕ) : Octad.ind (wSet δ) = bvec 24 δ := by
  funext i
  simp only [Octad.ind, wSet, Finset.mem_filter, Finset.mem_univ, true_and, bvec]

theorem card_wSet (δ : ℕ) : (wSet δ).card = popc 24 δ := by
  rw [← hammingNorm_bvec, ← ind_wSet]
  exact (hammingNorm_ind _).symm

theorem pauliQ_octW (a0 δ : ℕ) :
    pauliQ ⟨false, a0 ^^^ (if Model.popcN 24 δ / 2 % 2 == 1 then 63 else 0),
      Model.thetaN (a0 ^^^ (if Model.popcN 24 δ / 2 % 2 == 1 then 63 else 0)) ^^^ Model.dualN δ⟩ =
      rOct (toC a0) (wSet δ) := by
  have ha : aOct (toC a0) (wSet δ) = toC (a0 ^^^ (if Model.popcN 24 δ / 2 % 2 == 1 then 63 else 0)) := by
    rw [aOct, nOct, card_wSet, toC_xor, toC_ite, ΩC_eq_toC, popcN_eq_popc, boolZ_mod_two]
  have e : toSC ⟨false, a0 ^^^ (if Model.popcN 24 δ / 2 % 2 == 1 then 63 else 0),
      Model.thetaN (a0 ^^^ (if Model.popcN 24 δ / 2 % 2 == 1 then 63 else 0)) ^^^ Model.dualN δ⟩ =
      ⟨0, aOct (toC a0) (wSet δ), thetaD (aOct (toC a0) (wSet δ)) +
        Submodule.Quotient.mk (Octad.ind (wSet δ))⟩ := by
    refine SpinCoord.ext rfl ha.symm ?_
    rw [ha, thetaD_toC, ind_wSet, mk_bvec_eq_toD, ← toD_xor]
    rfl
  exact (congrArg spinEquiv e).trans (rOct_eq _ _).symm

theorem short_octW {a0 δ : ℕ} (h8 : Model.popcN 24 (Model.wordN a0) = 8)
    (hsub : δ &&& Model.wordN a0 = δ) (hev : Model.popcN 24 δ % 2 = 0) :
    IsShortCoord (coordOf (rOct (toC a0) (wSet δ))) := by
  have hw : hammingNorm ((toC a0 : C) : Fin 24 → ZMod 2) = 8 := by
    rw [coe_toC, hammingNorm_bvec, ← popcN_eq_popc]
    exact h8
  let D : OctadWord := ⟨toC a0, hw⟩
  have hsubset : wSet δ ⊆ octSupp D := by
    intro i hi
    simp only [wSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have h1 := congrArg (fun x => x.testBit i) hsub
    simp only [Nat.testBit_and] at h1
    have h2 : (Model.wordN a0).testBit i = true := by
      cases h : (Model.wordN a0).testBit i
      · rw [h, Bool.and_false, hi] at h1
        exact absurd h1 (by simp)
      · rfl
    change i ∈ supp ((toC a0 : C) : Fin 24 → ZMod 2)
    rw [mem_supp_iff, coe_toC]
    simp [bvec, h2]
  have hevenc : Even (wSet δ).card := by
    rw [card_wSet, ← popcN_eq_popc, Nat.even_iff]
    exact hev
  have hl := isShortCoord_labelElt (.inr (.inr (.inr ⟨D, Octad.cls (octSupp D) (wSet δ)⟩)))
  rw [labelElt, rOctQ_cls hsubset hevenc] at hl
  exact hl

theorem short_oct {a th d δ a0 w : ℕ} {ok8 : Bool} (hth : th = Model.thetaN a)
    (hw : w = Model.wordN a0) (hok : ok8 = true → Model.popcN 24 w = 8)
    (h : octOK a th d δ a0 w ok8 = true) : IsShortCoord (toC a, toD d) := by
  unfold octOK at h
  simp only [bAnd_true, beq_true] at h
  obtain ⟨h8, hsub, hc0, ha, hd⟩ := h
  have h8' := hok h8
  rw [hw] at h8' hsub
  simp only [popcT_eq] at hc0 ha
  have hev : Model.popcN 24 δ % 2 = 0 := by rw [← Nat.and_one_is_mod]; exact hc0
  have hsel : selB (Nat.land (Nat.shiftRight (Model.popcN 24 δ) (nat_lit 1)) (nat_lit 1)) (nat_lit 63) =
      if Model.popcN 24 δ / 2 % 2 == 1 then 63 else 0 := by
    change selB ((Model.popcN 24 δ >>> 1) &&& 1) 63 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one]
    rcases Nat.mod_two_eq_zero_or_one (Model.popcN 24 δ / 2) with h | h <;> simp [h, selB]
  rw [hsel] at ha
  have h := short_octW h8' hsub hev
  rw [← pauliQ_octW, coordOf_pauliQ'] at h
  rw [hd, hth, dualT_eq, ← ha]
  exact h

theorem short_pair {a d i j : ℕ} (h : pairOK a d i j = true) : IsShortCoord (toC a, toD d) := by
  unfold pairOK at h
  simp only [bRec_true, beq_true, blt_true, Bool.false_eq_true, and_false, or_false] at h
  obtain ⟨hij, hj, ha, hd⟩ := h
  rw [shl_one, shl_one, dualT_eq] at hd
  have hi : i < 24 := by omega
  have hne : (⟨i, hi⟩ : Fin 24) ≠ ⟨j, hj⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  have hlt : (⟨i, hi⟩ : Fin 24) < ⟨j, hj⟩ := Fin.mk_lt_mk.2 hij
  rcases ha with ⟨ha, -⟩ | ⟨-, ha⟩
  · rw [ha, hd]
    have h := isShortCoord_labelElt (.inl ⟨(⟨i, hi⟩, ⟨j, hj⟩), hlt⟩ : ShortLabel)
    have e := pauliQ_minus hne
    simp only [labelElt] at h
    rw [← e, coordOf_pauliQ'] at h
    exact h
  · rw [ha, hd]
    have h := isShortCoord_labelElt (.inr (.inl ⟨(⟨i, hi⟩, ⟨j, hj⟩), hlt⟩) : ShortLabel)
    have e := pauliQ_plus hne
    simp only [labelElt] at h
    rw [← e, coordOf_pauliQ'] at h
    exact h

theorem isShortCoord_of_entryOK {a d p : ℕ} (h : entryOK a (ctxOf a) d p = true) :
    IsShortCoord (toC a, toD d) := by
  unfold entryOK ctxOf at h
  dsimp only at h
  generalize Nat.beq (Nat.land (Nat.shiftRight p (nat_lit 24)) (nat_lit 1)) (nat_lit 1) = f at h
  generalize Nat.shiftRight p (nat_lit 28) = t at h
  rw [bRec_true, bRec_true, bRec_true] at h
  rcases h with ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩⟩
  · refine short_odd (thetaT_eq a) ?_ rfl h
    rw [nIf_eq, cOf, nIf_eq]
    split_ifs <;> exact wordT_eq _
  · cases f
    · exact short_oct (thetaT_eq a) (wordT_eq a) (fun h8 => by rw [← popcT_eq]; exact beq_true.1 h8) h
    · exact short_oct (thetaT_eq _) (wordT_eq _) (fun h8 => by rw [← popcT_eq]; exact beq_true.1 h8) h
  · exact short_pair h
  · exact absurd h (by simp)

end CertificateChecks.MonsterExist.ShortKey

end

module

public import Certificates.Kernel.KDenseP.M13
public import CFSG.Certificates.Kernel.KDenseP.M13.C16957
public import CFSG.Certificates.Kernel.KDenseP.M13.Rank16957
public import CFSG.Certificates.Kernel.Common.F2FixRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelKDenseP.M13.E16957

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.AxisCount
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.KC.KDenseP.M13 CFSG.KC.XorBits CFSG.KC.F2FixRank CFSG.KD.M13.r16957

set_option maxRecDepth 100000

theorem add_mul_xor {a b : ℕ} (c d : ℕ) (ha : a < 4096) (hb : b < 4096) :
    (a + 4096 * c) ^^^ (b + 4096 * d) = (a ^^^ b) + 4096 * (c ^^^ d) := by
  have ha' : a < 2 ^ 12 := ha
  have hb' : b < 2 ^ 12 := hb
  have e : ∀ x y : ℕ, x + 4096 * y = 2 ^ 12 * y + x := fun x y => by rw [Nat.add_comm]; rfl
  rw [e, e, e]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add c ha', Nat.testBit_two_pow_mul_add d hb',
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow ha' hb'), Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem code_mul {x y : Model.Pauli} (hx : validB x = true) (hy : validB y = true) :
    code (x.mul y) = code x ^^^ code y := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at hx hy
  obtain ⟨s, a, d⟩ := x
  obtain ⟨t, b, e⟩ := y
  exact (add_mul_xor d e hx.1 hy.1).symm

@[expose] def bP (i : ℕ) : Model.Pauli := if i < 12 then basisT i else basisD (i - 12)

@[expose] def iP (i : ℕ) : Model.Pauli := if i < 12 then imgT13[i]! else imgD13[i - 12]!

@[expose] def selP (f : ℕ → Model.Pauli) (v : ℕ) : ℕ → Model.Pauli
  | 0 => (false, 0, 0)
  | k + 1 => (selP f v k).mul (if v.testBit k then f k else (false, 0, 0))

theorem selP_spec {f : ℕ → Model.Pauli} (v : ℕ) :
    ∀ k, (∀ i < k, validB (f i) = true) →
      validB (selP f v k) = true ∧ code (selP f v k) = xorB (fun i => code (f i)) v k
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, hf => by
    obtain ⟨h1, h2⟩ := selP_spec v k fun i hi => hf i (Nat.lt_succ_of_lt hi)
    have hg : validB (if v.testBit k then f k else (false, 0, 0)) = true := by
      split_ifs
      · exact hf k (Nat.lt_succ_self k)
      · decide
    refine ⟨validB_mul h1 hg, ?_⟩
    rw [selP, code_mul h1 hg, h2, xorB_succ]
    congr 1
    split_ifs <;> rfl

theorem conj_selP {x : Gmat} {b m : ℕ → Model.Pauli} (v : ℕ) :
    ∀ k, (∀ i < k, x * rhoG (b i) = rhoG (m i) * x) →
      x * rhoG (selP b v k) = rhoG (selP m v k) * x
  | 0, _ => by simp only [selP, rhoG_one, mul_one, one_mul]
  | k + 1, h => by
    have ih := conj_selP v k fun i hi => h i (Nat.lt_succ_of_lt hi)
    have hk : x * rhoG (if v.testBit k then b k else (false, 0, 0)) =
        rhoG (if v.testBit k then m k else (false, 0, 0)) * x := by
      split_ifs
      · exact h k (Nat.lt_succ_self k)
      · rw [rhoG_one, mul_one, one_mul]
    rw [selP, selP, rhoG_mul, rhoG_mul, ← mul_assoc, hk, mul_assoc, ih, mul_assoc]

theorem validB_bP : ∀ i < 24, validB (bP i) = true := by decide +kernel

theorem validB_iP : ∀ i < 24, validB (iP i) = true := by decide +kernel

theorem code_bP : ∀ i < 24, code (bP i) = 2 ^ i := by decide +kernel

theorem code_iP : ∀ i < 24, code (iP i) = col i := by decide +kernel

theorem conj_z {x : Gmat} {T D T' D' : Model.Pauli} (hT : x * rhoG T = rhoG T' * x)
    (hD : x * rhoG D = rhoG D' * x)
    (h : D.mul T = Model.Pauli.mul (true, 0, 0) (T.mul D))
    (h' : D'.mul T' = Model.Pauli.mul (true, 0, 0) (T'.mul D')) :
    x * rhoG (true, 0, 0) = rhoG (true, 0, 0) * x := by
  have e1 : x * rhoG (T.mul D) = rhoG (T'.mul D') * x := by
    rw [rhoG_mul, rhoG_mul, ← mul_assoc, hD, mul_assoc, hT, mul_assoc]
  have e2 : x * rhoG (D.mul T) = rhoG (D'.mul T') * x := by
    rw [rhoG_mul, rhoG_mul, ← mul_assoc, hT, mul_assoc, hD, mul_assoc]
  rw [h, h', rhoG_mul (true, 0, 0) (T.mul D), rhoG_mul (true, 0, 0) (T'.mul D'), ← mul_assoc,
    e1, mul_assoc, mul_assoc] at e2
  exact mul_left_cancel e2

theorem split_sign (s : Bool) (P : Model.Pauli) :
    ((s, P.2.1, P.2.2) : Model.Pauli) = Model.Pauli.mul (s ^^ P.1, 0, 0) P := by
  obtain ⟨p, a, d⟩ := P
  simp only [Model.Pauli.mul, Model.Pauli.s, Model.Pauli.a, Model.Pauli.d,
    AxisCount.pairN_zero_right, Nat.zero_xor, Prod.mk.injEq, and_true]
  cases s <;> cases p <;> rfl

theorem agree16957 : agreeAll e16957 = true := (kd_m13% CFSG.KD.M13.c16957 e16957 []).1

theorem conj_bP : ∀ i < 24, gw genD13W1 * rhoG (bP i) = rhoG (iP i) * gw genD13W1 := by
  intro i hi
  have hagree : agreeAll (ebarPairs genD13W1 imgT13 imgD13) = true := agree16957
  by_cases h12 : i < 12
  · have := agreeAll_sound hagree _
      (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_range.2 h12, rfl⟩))
    simp only at this
    rw [show (Native.Gen.rho (basisT i) :: genD13W1) = [Native.Gen.rho (basisT i)] ++ genD13W1 from
      rfl, gw_append, gw_append] at this
    simp only [bP, iP, if_pos h12]
    exact this
  · have h' : i - 12 < 12 := by omega
    have := agreeAll_sound hagree _
      (List.mem_append_right _ (List.mem_map.2 ⟨i - 12, List.mem_range.2 h', rfl⟩))
    simp only at this
    rw [show (Native.Gen.rho (basisD (i - 12)) :: genD13W1) =
      [Native.Gen.rho (basisD (i - 12))] ++ genD13W1 from rfl, gw_append, gw_append] at this
    simp only [bP, iP, if_neg h12]
    exact this

theorem conj_z13 : gw genD13W1 * rhoG (true, 0, 0) = rhoG (true, 0, 0) * gw genD13W1 :=
  conj_z (conj_bP 0 (by norm_num)) (conj_bP 12 (by norm_num)) (by decide +kernel)
    (by decide +kernel)

theorem fix_code {s : Bool} {A D : ℕ} (hA : A < 4096) (hD : D < 4096)
    (hc : gw genD13W1 * rhoG (s, A, D) = rhoG (s, A, D) * gw genD13W1) :
    xorB col (A + 4096 * D) 24 = A + 4096 * D := by
  set x := gw genD13W1
  set v := A + 4096 * D with hv
  have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  have hv24 : v < 2 ^ 24 := by omega
  obtain ⟨vb, cb⟩ := selP_spec (f := bP) v 24 validB_bP
  obtain ⟨vi, ci⟩ := selP_spec (f := iP) v 24 validB_iP
  rw [xorB_congr_fun v 24 code_bP, xorB_two_pow hv24] at cb
  rw [xorB_congr_fun v 24 code_iP] at ci
  have hconj := conj_selP (x := x) v 24 conj_bP
  set P := selP bP v 24
  set P' := selP iP v 24
  have hPa : P.2.1 = A ∧ P.2.2 = D := by
    simp only [validB, Bool.and_eq_true, decide_eq_true_eq] at vb
    have h1 : P.2.1 + 4096 * P.2.2 = A + 4096 * D := cb
    omega
  have hsplit : ((s, A, D) : Model.Pauli) = Model.Pauli.mul (s ^^ P.1, 0, 0) P := by
    rw [← split_sign, hPa.1, hPa.2]
  have hS : ∀ t : Bool, x * rhoG (t, 0, 0) = rhoG (t, 0, 0) * x := by
    intro t
    cases t
    · rw [rhoG_one, mul_one, one_mul]
    · exact conj_z13
  have himg : x * rhoG (s, A, D) = rhoG (Model.Pauli.mul (s ^^ P.1, 0, 0) P') * x := by
    rw [hsplit, rhoG_mul, rhoG_mul, ← mul_assoc, hconj, mul_assoc, hS, mul_assoc]
  rw [himg] at hc
  have hvs : validB (s ^^ P.1, 0, 0) = true := by simp [validB]
  have e := eq_of_rhoG_eq (validB_mul hvs vi) (by simp [validB, hA, hD]) (mul_right_cancel hc)
  have e2 := congrArg code e
  rw [code_mul hvs vi, ci] at e2
  have e3 : code (s ^^ P.1, 0, 0) = 0 := rfl
  rw [e3, Nat.zero_xor] at e2
  exact e2

theorem c16957 :
    Nat.card ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer ({gw genD13W1} : Set Gmat)) ≤ 2 := by
  classical
  set x := gw genD13W1
  set F := (Finset.range (2 ^ 24)).filter fun v => xorB col v 24 = v
  have hF : F.card ≤ 1 := card_fix_le rank_ok
  let g : ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer {x}) → Bool × F := fun e =>
    let t := Classical.choose (exists_rhoG_eq ⟨e.1, (Subgroup.mem_inf.1 e.2).1⟩)
    (t.1, ⟨t.2.1 + 4096 * t.2.2, by
      have ht := Classical.choose_spec (exists_rhoG_eq ⟨e.1, (Subgroup.mem_inf.1 e.2).1⟩)
      have hc : x * (e : Gmat) = (e : Gmat) * x :=
        (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 e.2).2).symm
      rw [← ht] at hc
      have h1 := t.2.1.2
      have h2 := t.2.2.2
      have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), fix_code h1 h2 hc⟩⟩)
  have hginj : Function.Injective g := by
    intro e e' hee
    simp only [g, Prod.mk.injEq, Subtype.mk.injEq] at hee
    obtain ⟨hs, hn⟩ := hee
    set t := Classical.choose (exists_rhoG_eq ⟨e.1, (Subgroup.mem_inf.1 e.2).1⟩) with htdef
    set t' := Classical.choose (exists_rhoG_eq ⟨e'.1, (Subgroup.mem_inf.1 e'.2).1⟩) with ht'def
    have ht := Classical.choose_spec (exists_rhoG_eq ⟨e.1, (Subgroup.mem_inf.1 e.2).1⟩)
    have ht' := Classical.choose_spec (exists_rhoG_eq ⟨e'.1, (Subgroup.mem_inf.1 e'.2).1⟩)
    rw [← htdef] at ht
    rw [← ht'def] at ht'
    have h1 := t.2.1.2
    have h2 := t'.2.1.2
    have hA : (t.2.1 : ℕ) = t'.2.1 := by omega
    have hD : (t.2.2 : ℕ) = t'.2.2 := by omega
    have htt : t = t' := Prod.ext hs (Prod.ext (Fin.ext hA) (Fin.ext hD))
    apply Subtype.ext
    change (e : Gmat) = (e' : Gmat)
    rw [← ht, ← ht', htt]
  calc Nat.card ↥(rhoQ.subgroupOf Gmat ⊓ Subgroup.centralizer {x}) ≤ Nat.card (Bool × F) :=
        Nat.card_le_card_of_injective g hginj
    _ = 2 * F.card := by simp [Nat.card_prod]
    _ ≤ 2 := by omega

end CertificateChecks.KernelKDenseP.M13.E16957

end

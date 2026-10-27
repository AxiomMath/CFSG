
module

public import CFSG.Monster.B.TwoA.Sp8.LiftsInputs
public import CFSG.Certificates.Kernel.Common.BvecLoop
public import CFSG.Monster.B.TwoA.Census.CosetEnumGroup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.Sp8Fold

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible

theorem zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem liftP_comm : ∀ i j : Fin 8,
    Model.Pauli.mul (liftP i) (liftP j) = Model.Pauli.mul (liftP j) (liftP i) := by decide +kernel

theorem liftP_sq : ∀ i : Fin 8, Model.Pauli.mul (liftP i) (liftP i) = (false, 0, 0) := by
  decide +kernel

theorem liftP_conj : ∀ k : Fin 8, Model.conjYN 3 (liftP k) = liftP k := by decide +kernel

@[expose] noncomputable def fac (v : Fin 8 → ZMod 2) (k : Fin 8) : Q :=
  pauliQ (if v k = 1 then liftP k else (false, 0, 0))

theorem pauliQ_foldl (f : Model.Pauli → Fin 8 → Model.Pauli) (g : Fin 8 → Q)
    (hf : ∀ acc k, pauliQ (f acc k) = pauliQ acc * g k) (L : List (Fin 8)) :
    ∀ acc, pauliQ (L.foldl f acc) = pauliQ acc * (L.map g).prod := by
  induction L with
  | nil => exact fun acc => (mul_one _).symm
  | cons k L ih =>
    intro acc
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, hf, mul_assoc]

theorem pauliQ_foldP (v : Fin 8 → ZMod 2) :
    pauliQ (foldP v) = ((List.finRange 8).map (fac v)).prod := by
  unfold foldP
  rw [pauliQ_foldl _ (fac v) (fun acc k => ?_), pauliQ_false_zero, one_mul]
  by_cases h : v k = 1
  · rw [fac, ite_eq_left h, ite_eq_left h, pauliQ_mul]
  · rw [fac, ite_eq_right h, ite_eq_right h, pauliQ_false_zero, mul_one]

theorem commute_gen (i j : Fin 8) : Commute (pauliQ (liftP i)) (pauliQ (liftP j)) := by
  change pauliQ (liftP i) * pauliQ (liftP j) = pauliQ (liftP j) * pauliQ (liftP i)
  rw [← pauliQ_mul, ← pauliQ_mul, liftP_comm]

theorem sq_gen (i : Fin 8) : pauliQ (liftP i) * pauliQ (liftP i) = 1 := by
  rw [← pauliQ_mul, liftP_sq, pauliQ_false_zero]

theorem fac_eq (v : Fin 8 → ZMod 2) (k : Fin 8) :
    fac v k = pauliQ (liftP k) ∨ fac v k = 1 := by
  by_cases h : v k = 1
  · exact Or.inl (by rw [fac, ite_eq_left h])
  · exact Or.inr (by rw [fac, ite_eq_right h, pauliQ_false_zero])

theorem commute_fac (v w : Fin 8 → ZMod 2) (i j : Fin 8) : Commute (fac v i) (fac w j) := by
  rcases fac_eq v i with h | h
  · rcases fac_eq w j with h' | h'
    · rw [h, h']
      exact commute_gen i j
    · rw [h']
      exact Commute.one_right _
  · rw [h]
    exact Commute.one_left _

theorem step_add : ∀ k : Fin 8, ∀ b c : ZMod 2,
    (if b + c = 1 then liftP k else (false, 0, 0)) =
      Model.Pauli.mul (if b = 1 then liftP k else (false, 0, 0))
        (if c = 1 then liftP k else (false, 0, 0)) := by decide +kernel

theorem fac_add (v w : Fin 8 → ZMod 2) (k : Fin 8) : fac (v + w) k = fac v k * fac w k := by
  rw [fac, fac, fac, Pi.add_apply, step_add, pauliQ_mul]

theorem commute_prod {y : Q} {v : Fin 8 → ZMod 2} (h : ∀ k, Commute y (fac v k))
    (L : List (Fin 8)) : Commute y (L.map (fac v)).prod :=
  Commute.list_prod_right _ _ fun x hx => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
    exact h j

theorem prod_mul {G ι : Type*} [Monoid G] (a b c : ι → G) (habc : ∀ k, a k = b k * c k)
    (hcb : ∀ i j, Commute (c i) (b j)) (L : List ι) :
    (L.map a).prod = (L.map b).prod * (L.map c).prod := by
  induction L with
  | nil => simp only [List.map_nil, List.prod_nil, mul_one]
  | cons k L ih =>
    have hc : Commute (c k) (L.map b).prod := Commute.list_prod_right _ _ fun x hx => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      exact hcb k j
    rw [List.map_cons, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.prod_cons, ih, habc]
    exact hc.mul_mul_mul_comm _ _

theorem prod_fac_add (v w : Fin 8 → ZMod 2) (L : List (Fin 8)) :
    (L.map (fac (v + w))).prod = (L.map (fac v)).prod * (L.map (fac w)).prod :=
  prod_mul _ _ _ (fac_add v w) (commute_fac w v) L

theorem pauliQ_foldP_add (v w : Fin 8 → ZMod 2) :
    pauliQ (foldP (v + w)) = pauliQ (foldP v) * pauliQ (foldP w) := by
  rw [pauliQ_foldP, pauliQ_foldP, pauliQ_foldP, prod_fac_add]

theorem commute_foldP {y : Q} (h : ∀ k, Commute y (pauliQ (liftP k))) (v : Fin 8 → ZMod 2) :
    Commute y (pauliQ (foldP v)) := by
  rw [pauliQ_foldP]
  refine commute_prod (fun k => ?_) _
  rcases fac_eq v k with e | e
  · rw [e]
    exact h k
  · rw [e]
    exact Commute.one_right _

theorem fix_foldP (φ : Q ≃* Q) (h : ∀ k, φ (pauliQ (liftP k)) = pauliQ (liftP k))
    (v : Fin 8 → ZMod 2) : φ (pauliQ (foldP v)) = pauliQ (foldP v) := by
  have e : ⇑φ ∘ fac v = fac v := funext fun k => by
    rw [Function.comp_apply]
    rcases fac_eq v k with e | e
    · rw [e, h k]
    · rw [e, map_one]
  rw [pauliQ_foldP, map_list_prod, List.map_map, e]

theorem pauliQ_conjYN_foldP (v : Fin 8 → ZMod 2) :
    pauliQ (Model.conjYN 3 (foldP v)) = pauliQ (foldP v) := by
  rw [← conjQ_sign_toQ]
  refine fix_foldP _ (fun k => ?_) v
  rw [conjQ_sign_toQ, liftP_conj]

@[expose] def foldN (x : ℕ) : Model.Pauli :=
  (List.finRange 8).foldl (fun acc (k : Fin 8) =>
    if x.testBit k then Model.Pauli.mul acc (liftP k) else acc) (false, 0, 0)

theorem bvec_eq_one_iff (x : ℕ) (k : Fin 8) : bvec 8 x k = 1 ↔ x.testBit k = true := by
  rw [bvec_eq_boolZ, boolZ_eq_one_iff]

theorem foldl_bvec (x : ℕ) (L : List (Fin 8)) : ∀ acc : Model.Pauli,
    L.foldl (fun acc k => if bvec 8 x k = 1 then Model.Pauli.mul acc (liftP k) else acc) acc =
      L.foldl (fun acc (k : Fin 8) => if x.testBit k then Model.Pauli.mul acc (liftP k) else acc)
        acc := by
  induction L with
  | nil => exact fun _ => rfl
  | cons k L ih =>
    intro acc
    rw [List.foldl_cons, List.foldl_cons, ih]
    by_cases h : x.testBit k = true
    · rw [ite_eq_left ((bvec_eq_one_iff x k).2 h), ite_eq_left h]
    · rw [ite_eq_right (fun e => h ((bvec_eq_one_iff x k).1 e)), ite_eq_right h]

theorem foldP_bvec (x : ℕ) : foldP (bvec 8 x) = foldN x := foldl_bvec x _ _

theorem foldN_lt : ∀ x < 256, (foldN x).2.1 < 2 ^ 12 ∧ (foldN x).2.2 < 2 ^ 12 := by
  decide +kernel

theorem foldP_lt (v : Fin 8 → ZMod 2) : (foldP v).2.1 < 2 ^ 12 ∧ (foldP v).2.2 < 2 ^ 12 := by
  obtain ⟨x, hx, rfl⟩ := CFSG.KC.BvecLoop.exists_bvec 8 v
  rw [foldP_bvec]
  exact foldN_lt x hx

theorem ite_lt {b : Bool} {m : ℕ} (h : m < 2 ^ 12) : (if b = true then m else 0) < 2 ^ 12 := by
  split_ifs
  · exact h
  · positivity

theorem packN_lt (f : ℕ → Bool) : Model.packN f 12 < 2 ^ 12 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    rw [testBit_packN, decide_eq_false (Nat.not_lt.2 hi), Bool.false_and]

theorem thetaN_three_lt : Model.thetaN 3 < 2 ^ 12 := by decide +kernel

theorem conjYN_lt {y : Model.Pauli} (ha : y.2.1 < 2 ^ 12) (hd : y.2.2 < 2 ^ 12) :
    (Model.conjYN 3 y).2.1 < 2 ^ 12 ∧ (Model.conjYN 3 y).2.2 < 2 ^ 12 := by
  have h3 : (3 : ℕ) < 2 ^ 12 := by norm_num
  have h63 : (63 : ℕ) < 2 ^ 12 := by norm_num
  have h0 : (0 : ℕ) < 2 ^ 12 := by norm_num
  refine ⟨?_, ?_⟩
  · simp only [Model.conjYN, Model.Pauli.mul, Model.conjTN, Model.conjDN, Model.Pauli.a]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 (Nat.xor_lt_two_pow ha (ite_lt h63)))
      (Nat.xor_lt_two_pow (ite_lt h3) (ite_lt h63))
  · simp only [Model.conjYN, Model.Pauli.mul, Model.conjTN, Model.conjDN, Model.Pauli.d,
      Model.acodeN, Model.dualN]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow h0 (packN_lt _))
      (Nat.xor_lt_two_pow (ite_lt thetaN_three_lt) hd)

end CertificateChecks.Sp8Fold

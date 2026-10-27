
module

public import Certificates.Kernel.Misc.Tits.JOps8073

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.V

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT
open scoped commutatorElement

local instance decForallBool {p : Bool → Prop} [DecidablePred p] : Decidable (∀ b, p b) :=
  decidable_of_iff (p false ∧ p true)
    ⟨fun ⟨h1, h2⟩ b => by cases b <;> assumption, fun h => ⟨h _, h _⟩⟩

theorem test_spec {i cl : ℕ} (h : test i cl = true) :
    memN (lam 0 i) LAM = true ∧
    (Pb i = true → Nat.beq cl 0 = true ∧ sq i = true ∧ Nat.beq (lam 0 i) 0 = true ∧
      (allc i = true → isOne i = true ∨ isZ i = true)) ∧
    (Pb i = false → Nat.beq cl 0 = false ∧ Nat.beq (lam 0 i) 0 = false ∧
      Nat.beq (lam 4 i) (lam 0 i) = false ∧ cover i = true ∧ Nat.beq cl 1 = sq i) := by
  unfold test at h
  revert h
  generalize memN (lam 0 i) LAM = a0
  generalize Pb i = a1
  generalize Nat.beq cl 0 = a2
  generalize sq i = a3
  generalize Nat.beq (lam 0 i) 0 = a4
  generalize allc i = a5
  generalize isOne i = a6
  generalize isZ i = a7
  generalize Nat.beq (lam 4 i) (lam 0 i) = a8
  generalize cover i = a9
  generalize Nat.beq cl 1 = a10
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;>
    cases a7 <;> cases a8 <;> cases a9 <;> cases a10 <;> decide

theorem tst {i : ℕ} (hi : i < 512) : test i (cls i) = true := allN_spec enumK i hi

theorem Pb_cls {i : ℕ} (hi : i < 512) : Pb i = Nat.beq (cls i) 0 := by
  obtain ⟨-, h1, h2⟩ := test_spec (tst hi)
  cases h : Pb i
  · exact ((h2 h).1).symm
  · exact ((h1 h).1).symm

theorem Pb_lam {i : ℕ} (hi : i < 512) : Pb i = true ↔ lam 0 i = 0 := by
  obtain ⟨-, h1, h2⟩ := test_spec (tst hi)
  constructor
  · intro h
    exact Nat.eq_of_beq_eq_true (h1 h).2.2.1
  · intro h
    cases e : Pb i
    · have := (h2 e).2.1
      rw [h] at this
      exact absurd this (by decide)
    · rfl

theorem memN_iff (v : ℕ) : ∀ L : List ℕ, memN v L = true ↔ v ∈ L
  | [] => by simp [memN]
  | a :: L => by
    have e : memN v (a :: L) = Bool.rec (motive := fun _ => Bool) (memN v L) true (Nat.beq a v) :=
      rfl
    rw [e, List.mem_cons, ← memN_iff v L]
    cases h : Nat.beq a v
    · have : a ≠ v := fun e => by rw [e, Nat.beq_refl] at h; exact Bool.noConfusion h
      simp only
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm this
        · exact e
    · simp only [true_iff]
      exact Or.inl (Nat.eq_of_beq_eq_true h).symm

theorem allL_iff' (f : ℕ → Bool) : ∀ L : List ℕ, CFSG.KS.SporSch.allL f L = true ↔ ∀ x ∈ L, f x = true
  | [] => by simp [CFSG.KS.SporSch.allL]
  | a :: L => by
    have e : CFSG.KS.SporSch.allL f (a :: L) =
        Bool.rec (motive := fun _ => Bool) false (CFSG.KS.SporSch.allL f L) (f a) := rfl
    rw [e, List.forall_mem_cons, ← allL_iff' f L]
    cases f a <;> simp

open scoped Classical

@[expose] def enc (b0 b1 b2 b3 b4 : Bool) : ℕ :=
  Nat.add (Bool.rec (motive := fun _ => Nat) 1 0 b0) (Nat.add (Bool.rec (motive := fun _ => Nat) 2 0 b1)
    (Nat.add (Bool.rec (motive := fun _ => Nat) 4 0 b2) (Nat.add (Bool.rec (motive := fun _ => Nat) 8 0 b3)
      (Bool.rec (motive := fun _ => Nat) 16 0 b4))))

theorem enc_bit (b0 b1 b2 b3 b4 : Bool) : enc b0 b1 b2 b3 b4 < 32 ∧
    (enc b0 b1 b2 b3 b4).testBit 0 = !b0 ∧ (enc b0 b1 b2 b3 b4).testBit 1 = !b1 ∧
    (enc b0 b1 b2 b3 b4).testBit 2 = !b2 ∧ (enc b0 b1 b2 b3 b4).testBit 3 = !b3 ∧
    (enc b0 b1 b2 b3 b4).testBit 4 = !b4 := by
  revert b0 b1 b2 b3 b4
  decide

theorem lam_eq (j i : ℕ) : lam j i = enc (cm i (Bc j 0)) (cm i (Bc j 1)) (cm i (Bc j 2))
    (cm i (Bc j 3)) (cm i (Bc j 4)) := rfl

theorem lam_lt (j i : ℕ) : lam j i < 32 := by
  rw [lam_eq]
  exact (enc_bit _ _ _ _ _).1

theorem lam_bit (j i : ℕ) {m : ℕ} (hm : m < 5) : (lam j i).testBit m = !(cm i (Bc j m)) := by
  rw [lam_eq]
  obtain ⟨-, h0, h1, h2, h3, h4⟩ := enc_bit (cm i (Bc j 0)) (cm i (Bc j 1)) (cm i (Bc j 2))
    (cm i (Bc j 3)) (cm i (Bc j 4))
  interval_cases m
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem bits_eq {v w : ℕ} (hv : v < 32) (hw : w < 32) (h : ∀ m < 5, v.testBit m = w.testBit m) :
    v = w := by
  refine Nat.eq_of_testBit_eq fun m => ?_
  by_cases hm : m < 5
  · exact h m hm
  · have h32 : (32 : ℕ) ≤ 2 ^ m := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h32), Nat.testBit_lt_two_pow (lt_of_lt_of_le hw h32)]

theorem bool_not_of_iff {b : Bool} {P : Prop} (h : b = true ↔ P) : (!b) = decide (¬ P) := by
  cases b
  · have : ¬ P := fun p => Bool.false_ne_true (h.2 p)
    simp [this]
  · simp [h.1 rfl]

theorem eGI3 : GI 3 = CI := rfl

theorem cnC : Cn C := cFacts.2.2.2.2.1

theorem cnCI : Cn CI := by
  rw [← eGI3]
  exact (canK_at (k := 3) (by omega)).2.1

theorem rC : Rep 1755 (unpack 1755 11 C) cc := by
  rw [← cFacts.2.1]
  exact cFacts.2.2.1

theorem rCI : Rep 1755 (unpack 1755 11 CI) cc⁻¹ := by
  obtain ⟨-, -, c3, -⟩ := canK_at (k := 3) (by omega)
  have rg := gK_rep (k := 3) (by omega)
  have h := rep_inv_of_isInvA rg (invEqK_sound (n := 1755) (w := 11) c3).2
  have e : gK 3 = cc := by simp [gK]
  rw [e, eGI3] at h
  exact h

@[expose] noncomputable def bcg (j m : ℕ) : Equiv.Perm (Fin 1755) := cc ^ j * el (bI m) * (cc ^ j)⁻¹

theorem bI_lt {m : ℕ} (hm : m < 5) : bI m < 512 := by
  interval_cases m <;> decide

theorem bcg_zero (m : ℕ) : bcg 0 m = el (bI m) := by simp [bcg]

theorem bcg_succ (j m : ℕ) : bcg (j + 1) m = cc * bcg j m * cc⁻¹ := by
  simp only [bcg]
  group

theorem bcg_mem {m : ℕ} (hm : m < 5) : ∀ j, bcg j m ∈ titsJ
  | 0 => by rw [bcg_zero]; exact el_mem (bI_lt hm)
  | j + 1 => by rw [bcg_succ]; exact cc_norm (bcg_mem hm j)

theorem Bc_rep {m : ℕ} (hm : m < 5) : ∀ j, j < 5 → Rep 1755 (unpack 1755 11 (Bc j m)) (bcg j m)
  | 0, _ => by
    have e : Bc 0 m = Pk (bI m) := rfl
    rw [e, bcg_zero]
    exact Pk_rep (bI_lt hm)
  | j + 1, hj => by
    have ih := Bc_rep hm j (by omega)
    have cB : Cn (Bc j m) := allN_spec (allN_spec canB j (by omega)) m hm
    have e : Bc (j + 1) m = pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) C (Bc j m)) CI := rfl
    rw [e, ← cmpU (cmpC cnC cB) cnCI, ← cmpU cnC cB, bcg_succ]
    exact rep_compA (rep_compA rC ih) rCI

theorem cm_bc {i : ℕ} (hi : i < 512) {j m : ℕ} (hj : j < 5) (hm : m < 5) :
    cm i (Bc j m) = true ↔ Commute (el i) (bcg j m) :=
  cm_iff hi (Bc_rep hm j hj) (bcg_mem hm j)

theorem bm_mem {m : ℕ} (hm : m < 5) : el (bI m) ∈ Esub := by
  refine (Pb_iff (bI_lt hm)).1 ?_
  rw [Pb_cls (bI_lt hm)]
  interval_cases m <;> decide

theorem lam0_bit {i : ℕ} (hi : i < 512) {m : ℕ} (hm : m < 5) :
    (lam 0 i).testBit m = decide (¬ Commute (el (bI m)) (el i)) := by
  rw [lam_bit 0 i hm, bool_not_of_iff (cm_bc hi (by omega) hm), bcg_zero]
  simp only [Commute.symm_iff (a := el i)]

theorem memE_iff {x : Equiv.Perm (Fin 1755)} (hx : x ∈ titsJ) :
    x ∈ Esub ↔ ∀ m < 5, Commute (el (bI m)) x := by
  obtain ⟨i, hi, rfl⟩ := el_surj hx
  rw [← Pb_iff hi, Pb_lam hi]
  constructor
  · intro h m hm
    have := lam0_bit hi hm
    rw [h, Nat.zero_testBit] at this
    by_contra hc
    simp [hc] at this
  · intro h
    refine bits_eq (lam_lt 0 i) (by norm_num) fun m hm => ?_
    rw [lam0_bit hi hm, Nat.zero_testBit]
    simp [h m hm]

theorem lam0_zero_iff {i : ℕ} (hi : i < 512) : lam 0 i = 0 ↔ el i ∈ Esub := by
  rw [← Pb_lam hi, Pb_iff hi]

theorem lam0_mul {a b x : ℕ} (ha : a < 512) (hb : b < 512) (hx : x < 512)
    (h : el x = el a * el b) : lam 0 x = lam 0 a ^^^ lam 0 b := by
  refine bits_eq (lam_lt 0 x) (Nat.xor_lt_two_pow (n := 5) (lam_lt 0 a) (lam_lt 0 b))
    fun m hm => ?_
  rw [Nat.testBit_xor, lam0_bit hx hm, lam0_bit ha hm, lam0_bit hb hm, h,
    Grp.comm_mul_iff zFacts.1 zFacts.2.1 zFacts.2.2 (bm_mem hm) (el_mem ha) (el_mem hb)]
  by_cases p : Commute (el (bI m)) (el a) <;> by_cases q : Commute (el (bI m)) (el b) <;>
    simp [p, q]

theorem lam0_inv {a x : ℕ} (ha : a < 512) (hx : x < 512) (h : el x = (el a)⁻¹) :
    lam 0 x = lam 0 a := by
  refine bits_eq (lam_lt 0 x) (lam_lt 0 a) fun m hm => ?_
  rw [lam0_bit hx hm, lam0_bit ha hm, h, Commute.inv_right_iff]

theorem lam0_mulF (w y : Fin 512) : lam 0 (jOps.mul w y) = lam 0 w ^^^ lam 0 y :=
  lam0_mul w.2 y.2 (Fin.is_lt _) (el_mulF w y)

theorem lam0_invF (w : Fin 512) : lam 0 (jOps.inv w) = lam 0 w :=
  lam0_inv w.2 (Fin.is_lt _) (el_invF w)

theorem lam0_oneF : lam 0 jOps.one = 0 := by
  rw [lam0_zero_iff (Fin.is_lt _), el_oneF]
  exact Subgroup.one_mem _

theorem iterF (k : ℕ) (i : Fin 512) : el (jCc^[k] i) = cc ^ k * el i * (cc ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', el_ccF, ih]
    group

theorem cc_inv_pow {k j : ℕ} (hk : k < 5) (hj : j < 5) (hkj : (k + j) % 5 = 0) :
    (cc ^ k)⁻¹ = cc ^ j := by
  have h5 := cFacts.2.2.2.2.2
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← pow_add]
  rcases (by omega : k + j = 0 ∨ k + j = 5) with h | h <;> rw [h]
  · exact pow_zero _
  · exact h5

theorem comm_conj_iff {G : Type*} [Group G] (g a b : G) :
    Commute a (g * b * g⁻¹) ↔ Commute (g⁻¹ * a * g) b := by
  unfold Commute SemiconjBy
  constructor
  · intro h
    calc g⁻¹ * a * g * b = g⁻¹ * (a * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * a) * g := by rw [h]
      _ = b * (g⁻¹ * a * g) := by group
  · intro h
    calc a * (g * b * g⁻¹) = g * ((g⁻¹ * a * g) * b) * g⁻¹ := by group
      _ = g * (b * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * a := by group

theorem lam0_iter {k j : ℕ} (hk : k < 5) (hj : j < 5) (hkj : (k + j) % 5 = 0) (i : Fin 512) :
    lam 0 (jCc^[k] i) = lam j i := by
  refine bits_eq (lam_lt 0 _) (lam_lt j i) fun m hm => ?_
  rw [lam0_bit (Fin.is_lt _) hm, lam_bit j i hm, bool_not_of_iff (cm_bc i.2 hj hm), iterF,
    comm_conj_iff]
  have e : (cc ^ k)⁻¹ * el (bI m) * cc ^ k = bcg j m := by
    rw [bcg, ← cc_inv_pow hk hj hkj, inv_inv]
  rw [e, Commute.symm_iff (a := bcg j m)]

theorem appL_eq (M : List ℕ) : ∀ L : List ℕ, appL L M = L ++ M
  | [] => rfl
  | a :: L => by
    have e : appL (a :: L) M = a :: appL L M := rfl
    rw [e, appL_eq M L]
    rfl

theorem xorL_eq (v : ℕ) : ∀ L : List ℕ, xorL v L = L.map fun a => a ^^^ v
  | [] => rfl
  | a :: L => by
    have e : xorL v (a :: L) = Nat.xor a v :: xorL v L := rfl
    rw [e, xorL_eq v L]
    rfl

theorem spanF_cons (v : ℕ) (vs L : List ℕ) : spanF (v :: vs) L = spanF vs (appL L (xorL v L)) :=
  rfl

theorem words_map (i : Fin 512) : ∀ (ks : List ℕ) (W : List (Fin 512)),
    (ks.foldl (fun W k => W ++ W.map fun w => jOps.mul w (jCc^[k] i)) W).map
        (fun w : Fin 512 => lam 0 (w : ℕ)) =
      spanF (ks.map fun k => lam 0 (jCc^[k] i : ℕ)) (W.map fun w : Fin 512 => lam 0 (w : ℕ))
  | [], _ => rfl
  | k :: ks, W => by
    rw [List.foldl_cons, words_map i ks, List.map_cons, spanF_cons, appL_eq, xorL_eq,
      List.map_append, List.map_map, List.map_map]
    congr 2
    refine List.map_congr_left fun w _ => ?_
    simp only [Function.comp_apply]
    exact lam0_mulF w _

theorem wordsOf_labels (i : Fin 512) :
    (wordsOf jOps.mul jOps.one jCc i).map (fun w : Fin 512 => lam 0 (w : ℕ)) =
      spanF [lam 0 i, lam 4 i, lam 3 i, lam 2 i, lam 1 i] [0] := by
  unfold wordsOf
  rw [words_map i (List.range 5) [jOps.one]]
  have r5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
  rw [r5]
  simp only [List.map_cons, List.map_nil]
  rw [lam0_oneF, lam0_iter (k := 0) (j := 0) (by norm_num) (by norm_num) (by norm_num),
    lam0_iter (k := 1) (j := 4) (by norm_num) (by norm_num) (by norm_num),
    lam0_iter (k := 2) (j := 3) (by norm_num) (by norm_num) (by norm_num),
    lam0_iter (k := 3) (j := 2) (by norm_num) (by norm_num) (by norm_num),
    lam0_iter (k := 4) (j := 1) (by norm_num) (by norm_num) (by norm_num)]

end CertificateChecks.KernelMisc.TitsJT.V

end

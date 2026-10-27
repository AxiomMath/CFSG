module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtYF
public import Certificates.Kernel.Sporadic.OddCore.SuzBtXG
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.PcompFacts
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtYG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.SuzL34Cert
open CertificateChecks.KernelSpor.SuzBtXF CertificateChecks.KernelSpor.SuzBtXK
open CertificateChecks.KernelSpor.SuzBtXG CertificateChecks.KernelSpor.SuzBtYF

local notation "pg4" => pg 4 (mask 4)

theorem nIf_ite (c : Bool) (t e : Nat) : nIf(c, t, e) = if c = true then t else e := by
  cases c <;> rfl

theorem bt_eq (m k : Nat) : bt m k = m.testBit k := by
  unfold bt
  have e : Nat.land (Nat.shiftRight m k) 1 = m / 2 ^ k % 2 := by
    change (m >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ k) with h | h <;> rw [h] <;> rfl

theorem testBit_nIf (c : Bool) (v j : Nat) : (nIf(c, v, 0)).testBit j = (c && v.testBit j) := by
  cases c
  · exact Nat.zero_testBit j
  · rfl

theorem testBit_cmb (v0 v1 v2 v3 m j : Nat) : (cmb v0 v1 v2 v3 m).testBit j =
    ((m.testBit 0 && v0.testBit j) ^^ ((m.testBit 1 && v1.testBit j) ^^
      ((m.testBit 2 && v2.testBit j) ^^ (m.testBit 3 && v3.testBit j)))) := by
  unfold cmb
  change (nIf(bt m 0, v0, 0) ^^^ (nIf(bt m 1, v1, 0) ^^^
    (nIf(bt m 2, v2, 0) ^^^ nIf(bt m 3, v3, 0)))).testBit j = _
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, testBit_nIf, testBit_nIf, testBit_nIf,
    testBit_nIf, bt_eq, bt_eq, bt_eq, bt_eq]

theorem cmb_xor (v0 v1 v2 v3 m m' : Nat) :
    cmb v0 v1 v2 v3 (Nat.xor m m') = Nat.xor (cmb v0 v1 v2 v3 m) (cmb v0 v1 v2 v3 m') := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (cmb v0 v1 v2 v3 (m ^^^ m')).testBit j =
    (cmb v0 v1 v2 v3 m ^^^ cmb v0 v1 v2 v3 m').testBit j
  rw [Nat.testBit_xor, testBit_cmb, testBit_cmb, testBit_cmb]
  simp only [Nat.testBit_xor]
  generalize m.testBit 0 = x0
  generalize m.testBit 1 = x1
  generalize m.testBit 2 = x2
  generalize m.testBit 3 = x3
  generalize m'.testBit 0 = y0
  generalize m'.testBit 1 = y1
  generalize m'.testBit 2 = y2
  generalize m'.testBit 3 = y3
  generalize v0.testBit j = z0
  generalize v1.testBit j = z1
  generalize v2.testBit j = z2
  generalize v3.testBit j = z3
  revert x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3
  decide

theorem cmb_bits {m : Nat} (v0 v1 v2 v3 : Nat) (b0 b1 b2 b3 : Bool) (h0 : m.testBit 0 = b0)
    (h1 : m.testBit 1 = b1) (h2 : m.testBit 2 = b2) (h3 : m.testBit 3 = b3) (j : Nat) :
    (cmb v0 v1 v2 v3 m).testBit j = ((b0 && v0.testBit j) ^^ ((b1 && v1.testBit j) ^^
      ((b2 && v2.testBit j) ^^ (b3 && v3.testBit j)))) := by
  rw [testBit_cmb, h0, h1, h2, h3]

theorem cmb_zero (v0 v1 v2 v3 : Nat) : cmb v0 v1 v2 v3 0 = 0 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [cmb_bits v0 v1 v2 v3 false false false false (by decide) (by decide) (by decide)
      (by decide), Nat.zero_testBit]
    rfl

theorem cmb_one (v0 v1 v2 v3 : Nat) : cmb v0 v1 v2 v3 1 = v0 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [cmb_bits v0 v1 v2 v3 true false false false (by decide) (by decide) (by decide)
      (by decide)]
    cases v0.testBit j <;> rfl

theorem cmb_two (v0 v1 v2 v3 : Nat) : cmb v0 v1 v2 v3 2 = v1 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [cmb_bits v0 v1 v2 v3 false true false false (by decide) (by decide) (by decide)
      (by decide)]
    cases v1.testBit j <;> rfl

theorem cmb_four (v0 v1 v2 v3 : Nat) : cmb v0 v1 v2 v3 4 = v2 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [cmb_bits v0 v1 v2 v3 false false true false (by decide) (by decide) (by decide)
      (by decide)]
    cases v2.testBit j <;> rfl

theorem cmb_eight (v0 v1 v2 v3 : Nat) : cmb v0 v1 v2 v3 8 = v3 :=
  Nat.eq_of_testBit_eq fun j => by
    rw [cmb_bits v0 v1 v2 v3 false false false true (by decide) (by decide) (by decide)
      (by decide)]
    cases v3.testBit j <;> rfl

theorem cmb_fifteen (v0 v1 v2 v3 : Nat) :
    cmb v0 v1 v2 v3 15 = Nat.xor (Nat.xor v0 v1) (Nat.xor v2 v3) :=
  Nat.eq_of_testBit_eq fun j => by
    rw [cmb_bits v0 v1 v2 v3 true true true true (by decide) (by decide) (by decide)
      (by decide)]
    change _ = ((v0 ^^^ v1) ^^^ (v2 ^^^ v3)).testBit j
    simp only [Nat.testBit_xor]
    cases v0.testBit j <;> cases v1.testBit j <;> cases v2.testBit j <;> cases v3.testBit j <;> rfl

theorem cmb_nIf (v0 v1 v2 v3 : Nat) (c : Bool) (x : Nat) :
    cmb v0 v1 v2 v3 (nIf(c, x, 0)) = nIf(c, cmb v0 v1 v2 v3 x, 0) := by
  cases c
  · exact cmb_zero v0 v1 v2 v3
  · rfl

theorem cmb_cmb (v0 v1 v2 v3 m0 m1 m2 m3 m : Nat) :
    cmb v0 v1 v2 v3 (cmb m0 m1 m2 m3 m) = cmb (cmb v0 v1 v2 v3 m0) (cmb v0 v1 v2 v3 m1)
      (cmb v0 v1 v2 v3 m2) (cmb v0 v1 v2 v3 m3) m := by
  have e : cmb m0 m1 m2 m3 m = Nat.xor (nIf(bt m 0, m0, 0)) (Nat.xor (nIf(bt m 1, m1, 0))
      (Nat.xor (nIf(bt m 2, m2, 0)) (nIf(bt m 3, m3, 0)))) := rfl
  rw [e, cmb_xor, cmb_xor, cmb_xor, cmb_nIf, cmb_nIf, cmb_nIf, cmb_nIf]
  rfl

theorem xor_lt16 {x y : Nat} (hx : x < 16) (hy : y < 16) : Nat.xor x y < 16 :=
  Nat.xor_lt_two_pow (n := 4) hx hy

theorem nIf_lt {c : Bool} {v : Nat} (hv : v < 16) : nIf(c, v, 0) < 16 := by
  cases c
  · exact Nat.zero_lt_succ _
  · exact hv

theorem cmb_lt {v0 v1 v2 v3 : Nat} (m : Nat) (h0 : v0 < 16) (h1 : v1 < 16) (h2 : v2 < 16)
    (h3 : v3 < 16) : cmb v0 v1 v2 v3 m < 16 :=
  xor_lt16 (nIf_lt h0) (xor_lt16 (nIf_lt h1) (xor_lt16 (nIf_lt h2) (nIf_lt h3)))

theorem xor_eq_of {x y : Nat} (h : Nat.xor x y = 0) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  have e := congrArg (fun n => Nat.testBit n j) h
  change (x ^^^ y).testBit j = (0 : Nat).testBit j at e
  rw [Nat.testBit_xor, Nat.zero_testBit] at e
  revert e
  cases x.testBit j <;> cases y.testBit j <;> decide

theorem xor_rot (p q r t u : Nat) :
    Nat.xor (Nat.xor (Nat.xor q r) (Nat.xor t u)) p =
      Nat.xor (Nat.xor (Nat.xor p q) (Nat.xor r t)) u := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (((q ^^^ r) ^^^ (t ^^^ u)) ^^^ p).testBit j = (((p ^^^ q) ^^^ (r ^^^ t)) ^^^ u).testBit j
  simp only [Nat.testBit_xor]
  cases p.testBit j <;> cases q.testBit j <;> cases r.testBit j <;> cases t.testBit j <;>
    cases u.testBit j <;> rfl

theorem testBit_add_disj {x y : Nat} (h : ∀ j, x.testBit j = false ∨ y.testBit j = false) :
    x + y = x ||| y := by
  have h0 : x &&& y = 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.zero_testBit]
    rcases h j with e | e <;> simp [e]
  have hab : x + y < 2 ^ (x + y) := Nat.lt_two_pow_self
  have ha : x < 2 ^ (x + y) := lt_of_le_of_lt (by omega) hab
  have hb : y < 2 ^ (x + y) := lt_of_le_of_lt (by omega) hab
  have h1 : BitVec.ofNat (x + y) x &&& BitVec.ofNat (x + y) y = 0#(x + y) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb, h0, BitVec.toNat_zero]
  have key := congrArg BitVec.toNat (BitVec.add_eq_or_of_and_eq_zero _ _ h1)
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hab] at key
  exact key

theorem testBit_of_fld {X : Nat} {F : Nat → Nat} (hX : CFSG.KS.PF.Fld 4 X F)
    (hF : ∀ i, F i < 16) (j : Nat) : X.testBit j = (F (j / 4)).testBit (j % 4) := by
  have h := CFSG.KS.PF.testBit_pgM 4 X (j / 4) (j % 4)
  rw [CFSG.KS.PF.pg_of_fld hX (hF _), decide_eq_true (Nat.mod_lt j (by norm_num)), Bool.true_and,
    Nat.div_add_mod] at h
  exact h.symm

theorem fld_tabR (P V Q : Nat → Nat) (hP : ∀ m < 16, P m < 16 ∧ Q (P m) = m)
    (hQ : ∀ i < 16, Q i < 16 ∧ P (Q i) = i) (hV : ∀ m, V m < 16) :
    ∀ k ≤ 16, CFSG.KS.PF.Fld 4 (Nat.rec (motive := fun _ => Nat) 0
      (fun m ih => Nat.add ih (Nat.shiftLeft (V m) (Nat.mul 4 (P m)))) k)
      (fun i => if i < 16 ∧ Q i < k then V (Q i) else 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_zero 4) (fun i => ?_)
    simp
  | succ k ih =>
    intro hk
    have hX := ih (by omega)
    have hpk := hP k (by omega)
    have hY : CFSG.KS.PF.Fld 4 (Nat.shiftLeft (V k) (Nat.mul 4 (P k)))
        (fun i => if P k ≤ i then (if i - P k = 0 then V k else 0) else 0) :=
      CFSG.KS.PF.fld_shl (P k) (CFSG.KS.PF.fld_one (hV k))
    have hzero : (if P k < 16 ∧ Q (P k) < k then V (Q (P k)) else 0) = 0 := by
      rw [hpk.2]
      simp
    have hdisj : ∀ j, (Nat.rec (motive := fun _ => Nat) 0
        (fun m ih => Nat.add ih (Nat.shiftLeft (V m) (Nat.mul 4 (P m)))) k).testBit j = false ∨
        (Nat.shiftLeft (V k) (Nat.mul 4 (P k))).testBit j = false := by
      intro j
      rw [testBit_of_fld hX (fun i => by split_ifs <;> first | exact hV _ | norm_num) j,
        testBit_of_fld hY (fun i => by split_ifs <;> first | exact hV _ | norm_num) j]
      by_cases e : j / 4 = P k
      · left
        rw [e, hzero]
        exact Nat.zero_testBit _
      · right
        have h2 : (if P k ≤ j / 4 then (if j / 4 - P k = 0 then V k else 0) else 0) = 0 := by
          split_ifs <;> first | rfl | omega
        rw [h2]
        exact Nat.zero_testBit _
    have e : Nat.rec (motive := fun _ => Nat) 0
        (fun m ih => Nat.add ih (Nat.shiftLeft (V m) (Nat.mul 4 (P m)))) (k + 1) =
        (Nat.rec (motive := fun _ => Nat) 0
          (fun m ih => Nat.add ih (Nat.shiftLeft (V m) (Nat.mul 4 (P m)))) k) |||
          Nat.shiftLeft (V k) (Nat.mul 4 (P k)) := testBit_add_disj hdisj
    rw [e]
    refine CFSG.KS.PF.fld_congr (CFSG.KS.PF.fld_or hX hY) (fun i => ?_)
    by_cases hi : i = P k
    · subst hi
      rw [hzero]
      simp [hpk.1, hpk.2]
    · have h2 : (if P k ≤ i then (if i - P k = 0 then V k else 0) else 0) = 0 := by
        split_ifs <;> first | rfl | omega
      rw [h2, Nat.or_zero]
      by_cases h16 : i < 16
      · have hq := hQ i h16
        have hne : Q i ≠ k := fun e => hi (by rw [← hq.2, e])
        have hlt : Q i < k ↔ Q i < k + 1 := by omega
        simp only [h16, true_and, hlt]
      · simp [h16]

def pt (x : Nat) : Fin 16 := ⟨x % 16, Nat.mod_lt _ (by norm_num)⟩

theorem pt_val {x : Nat} (hx : x < 16) : (pt x).val = x := Nat.mod_eq_of_lt hx

theorem pt_fin (p : Fin 16) : pt p.val = p := Fin.ext (pt_val p.2)

theorem pt_inj {x y : Nat} (hx : x < 16) (hy : y < 16) (h : pt x = pt y) : x = y := by
  rw [← pt_val hx, ← pt_val hy, h]

theorem pt_xor {x y : Nat} (hx : x < 16) (hy : y < 16) :
    pt (Nat.xor x y) = xor16 (pt x) (pt y) := by
  apply Fin.ext
  rw [pt_val (xor_lt16 hx hy)]
  change Nat.xor x y = Nat.xor (pt x).val (pt y).val
  rw [pt_val hx, pt_val hy]

noncomputable def gv (g : Equiv.Perm (Fin 16)) (x : Nat) : Nat := (g (pt x)).val

theorem gv_lt (g : Equiv.Perm (Fin 16)) (x : Nat) : gv g x < 16 := (g (pt x)).isLt

theorem gv_fin (g : Equiv.Perm (Fin 16)) (p : Fin 16) : gv g p.val = (g p).val := by
  unfold gv
  rw [pt_fin]

theorem g_pt (g : Equiv.Perm (Fin 16)) (x : Nat) : g (pt x) = pt (gv g x) :=
  (pt_fin _).symm

section Lin

variable {g : Equiv.Perm (Fin 16)} (hadd : ∀ a b : Fin 16, g (xor16 a b) = xor16 (g a) (g b))
include hadd

theorem gv_xor {x y : Nat} (hx : x < 16) (hy : y < 16) :
    gv g (Nat.xor x y) = Nat.xor (gv g x) (gv g y) := by
  unfold gv
  rw [pt_xor hx hy, hadd]
  rfl

theorem g_zero : g 0 = 0 := by
  have h := hadd 0 0
  have e : xor16 0 0 = 0 := by decide
  rw [e] at h
  apply Fin.ext
  have h' := congrArg Fin.val h
  change (g 0).val = (g 0).val ^^^ (g 0).val at h'
  rw [Nat.xor_self] at h'
  exact h'

theorem gv_zero : gv g 0 = 0 := by
  unfold gv
  have e : pt 0 = 0 := rfl
  rw [e, g_zero hadd]
  rfl

theorem gv_nIf (c : Bool) (v : Nat) : gv g (nIf(c, v, 0)) = nIf(c, gv g v, 0) := by
  cases c
  · exact gv_zero hadd
  · rfl

theorem gv_cmb {v0 v1 v2 v3 : Nat} (h0 : v0 < 16) (h1 : v1 < 16) (h2 : v2 < 16) (h3 : v3 < 16)
    (m : Nat) : gv g (cmb v0 v1 v2 v3 m) = cmb (gv g v0) (gv g v1) (gv g v2) (gv g v3) m := by
  have e : cmb v0 v1 v2 v3 m = Nat.xor (nIf(bt m 0, v0, 0)) (Nat.xor (nIf(bt m 1, v1, 0))
      (Nat.xor (nIf(bt m 2, v2, 0)) (nIf(bt m 3, v3, 0)))) := rfl
  rw [e, gv_xor hadd (nIf_lt h0) (xor_lt16 (nIf_lt h1) (xor_lt16 (nIf_lt h2) (nIf_lt h3))),
    gv_xor hadd (nIf_lt h1) (xor_lt16 (nIf_lt h2) (nIf_lt h3)),
    gv_xor hadd (nIf_lt h2) (nIf_lt h3), gv_nIf hadd, gv_nIf hadd, gv_nIf hadd, gv_nIf hadd]
  rfl

end Lin

def ev (x : Fin 16) : Fin 4 → ZMod 2 := fun k => if x.val.testBit k.val then 1 else 0

theorem ev_inj : ∀ x y : Fin 16, ev x = ev y → x = y := by decide +kernel

theorem ev_xor : ∀ x y : Fin 16, ev (xor16 x y) = ev x + ev y := by decide +kernel

theorem ev_zero : ev 0 = 0 := by decide +kernel

theorem ev_neg : ∀ x : Fin 16, -ev x = ev x := by decide +kernel

theorem card_dvd16 (S : Finset (Fin 16)) (h0 : (0 : Fin 16) ∈ S)
    (hx : ∀ x ∈ S, ∀ y ∈ S, xor16 x y ∈ S) : S.card ∣ 16 := by
  let H : AddSubgroup (Fin 4 → ZMod 2) :=
    { carrier := ev '' (S : Set (Fin 16))
      add_mem' := by
        rintro _ _ ⟨x, hxS, rfl⟩ ⟨y, hyS, rfl⟩
        exact ⟨xor16 x y, hx x hxS y hyS, ev_xor x y⟩
      zero_mem' := ⟨0, h0, ev_zero⟩
      neg_mem' := by
        rintro _ ⟨x, hxS, rfl⟩
        exact ⟨x, hxS, (ev_neg x).symm⟩ }
  have h1 := AddSubgroup.card_addSubgroup_dvd_card H
  have h2 : Nat.card H = S.card := by
    change Nat.card (ev '' (S : Set (Fin 16))) = S.card
    rw [Nat.card_image_of_injective (fun x y h => ev_inj x y h)]
    simp
  have h3 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_eq_fintype_card]
    simp
  rw [← h2, ← h3]
  exact h1

section Order

variable {g : Equiv.Perm (Fin 16)} (hadd : ∀ a b : Fin 16, g (xor16 a b) = xor16 (g a) (g b))
  (ho : orderOf g = 5)

omit hadd in
include ho in
theorem pow5 : g ^ 5 = 1 := ho ▸ pow_orderOf_eq_one g

omit hadd in
include ho in
theorem g5 (y : Fin 16) : g (g (g (g (g y)))) = y := by
  have h := congrArg (fun f : Equiv.Perm (Fin 16) => f y) (pow5 ho)
  simpa [pow_succ, Equiv.Perm.mul_apply] using h

include hadd ho

theorem fix_zero {x : Fin 16} (hx : g x = x) : x = 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set F := Finset.univ.filter (fun y : Fin 16 => g y = y) with hF
  have hc : g.supportᶜ = F := by
    ext y
    simp [hF, Equiv.Perm.mem_support]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := g)
    (by rw [pow_one]; exact pow5 ho)
  rw [hc, Fintype.card_fin] at hmod
  have hd : F.card ∣ 16 := card_dvd16 F (by simp [hF, g_zero hadd]) (fun y hy z hz => by
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hy hz ⊢
    rw [hadd, hy, hz])
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show F.card ∣ 2 ^ 4 from hd)
  have h1 : F.card = 1 := by
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · simpa using hk'
    · rw [hk'] at hmod
      exact absurd hmod (by decide)
    · rw [hk'] at hmod
      exact absurd hmod (by decide)
    · rw [hk'] at hmod
      exact absurd hmod (by decide)
    · exfalso
      have hu : F = Finset.univ := Finset.eq_univ_of_card F (by rw [hk']; rfl)
      have e1 : g = 1 := Equiv.ext fun y => by
        have hy : y ∈ F := hu ▸ Finset.mem_univ y
        simpa [hF] using hy
      rw [e1, orderOf_one] at ho
      exact absurd ho (by decide)
  obtain ⟨z, hz⟩ := Finset.card_eq_one.1 h1
  have hx' : x ∈ F := by simp [hF, hx]
  have h0' : (0 : Fin 16) ∈ F := by simp [hF, g_zero hadd]
  rw [hz, Finset.mem_singleton] at hx' h0'
  rw [hx', h0']

theorem alg : ∃ a b c : Nat, 0 < a ∧ a < 16 ∧ 0 < b ∧ b < 16 ∧ 0 < c ∧ c < 16 ∧
    indep a b c = true ∧ tab a b c >>> (16 * 4) = 0 ∧ ∀ p : Fin 16, pg4 (tab a b c) p = g p := by
  set A := g 1 with hA
  set B := g A with hB
  set C := g B with hC
  set a := A.val
  set b := B.val
  set c := C.val
  have hne : ∀ y : Fin 16, y ≠ 0 → g y ≠ 0 := fun y hy e =>
    hy (g.injective (e.trans (g_zero hadd).symm))
  have hA0 : A ≠ 0 := hne 1 (by decide)
  have hB0 : B ≠ 0 := hne A hA0
  have hC0 : C ≠ 0 := hne B hB0
  have ha : a < 16 := A.isLt
  have hb : b < 16 := B.isLt
  have hc : c < 16 := C.isLt
  have g1 : gv g 1 = a := gv_fin g 1
  have ga : gv g a = b := gv_fin g A
  have gb : gv g b = c := gv_fin g B
  set d := Nat.xor (Nat.xor 1 a) (Nat.xor b c) with hd
  have hd16 : d < 16 := xor_lt16 (xor_lt16 (by norm_num) ha) (xor_lt16 hb hc)
  have gD : gv g (gv g c) = 1 := by
    have e := g5 ho 1
    have gc' : gv g c = (g C).val := gv_fin g C
    rw [gc', gv_fin g (g C)]
    change (g (g (g (g (g 1))))).val = 1
    rw [e]
    rfl
  have gc : gv g c = d := by
    set D := gv g c
    have hD : D < 16 := gv_lt g c
    have hs : gv g (Nat.xor d D) = Nat.xor d D := by
      rw [gv_xor hadd hd16 hD, hd, gv_xor hadd (xor_lt16 (by norm_num) ha) (xor_lt16 hb hc),
        gv_xor hadd (by norm_num) ha, gv_xor hadd hb hc, g1, ga, gb, gD]
      exact xor_rot 1 a b c D
    have hfix : g (pt (Nat.xor d D)) = pt (Nat.xor d D) := by
      rw [g_pt, hs]
    have h0 := fix_zero hadd ho hfix
    have h0' : Nat.xor d D = 0 := by
      have := congrArg Fin.val h0
      rw [pt_val (xor_lt16 hd16 hD)] at this
      exact this
    exact (xor_eq_of h0').symm
  let P : Nat → Nat := cmb 1 a b c
  let V : Nat → Nat := cmb a b c d
  have hP16 : ∀ m, P m < 16 := fun m => cmb_lt m (by norm_num) ha hb hc
  have hV16 : ∀ m, V m < 16 := fun m => cmb_lt m ha hb hc hd16
  have gP : ∀ m, gv g (P m) = V m := fun m => by
    change gv g (cmb 1 a b c m) = cmb a b c d m
    rw [gv_cmb hadd (by norm_num) ha hb hc, g1, ga, gb, gc]
  have hVP : ∀ m, V m = P (cmb 2 4 8 15 m) := fun m => by
    change cmb a b c d m = cmb 1 a b c (cmb 2 4 8 15 m)
    rw [cmb_cmb]
    rw [cmb_two, cmb_four, cmb_eight, cmb_fifteen]
  let S : Finset (Fin 16) := Finset.univ.image (fun m : Fin 16 => pt (P m.val))
  have memS : ∀ x, x ∈ S ↔ ∃ m < 16, pt (P m) = x := fun x => by
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨m, hm⟩ => ⟨m.val, m.isLt, hm⟩, fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩⟩
  have h0S : (0 : Fin 16) ∈ S := (memS 0).2 ⟨0, by norm_num, by
    change pt (cmb 1 a b c 0) = 0
    rw [cmb_zero]
    rfl⟩
  have hxS : ∀ x ∈ S, ∀ y ∈ S, xor16 x y ∈ S := by
    intro x hx y hy
    obtain ⟨m, hm, rfl⟩ := (memS x).1 hx
    obtain ⟨m', hm', rfl⟩ := (memS y).1 hy
    refine (memS _).2 ⟨Nat.xor m m', xor_lt16 hm hm', ?_⟩
    change pt (cmb 1 a b c (Nat.xor m m')) = _
    rw [cmb_xor]
    exact pt_xor (hP16 m) (hP16 m')
  have hgS : ∀ x ∈ S, g x ∈ S := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := (memS x).1 hx
    refine (memS _).2 ⟨cmb 2 4 8 15 m, cmb_lt m (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), ?_⟩
    rw [g_pt, gP, hVP]
  have hS : ∀ x, x ∈ S ↔ g x ∈ S := fun x =>
    ⟨hgS x, fun h => by
      have e := g5 ho x
      rw [← e]
      exact hgS _ (hgS _ (hgS _ (hgS _ h)))⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let σ : Equiv.Perm {x // x ∈ S} := g.subtypePerm fun x => (hS x).symm
  have hσ : σ ^ 5 = 1 := by
    ext ⟨y, hy⟩
    simp [σ, Equiv.Perm.subtypePerm_pow, pow5 ho]
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ)
    (by rw [pow_one]; exact hσ)
  have hsupp : σ.supportᶜ.card = 1 := by
    refine Finset.card_eq_one.2 ⟨⟨0, h0S⟩, ?_⟩
    ext ⟨y, hy⟩
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, ne_eq, not_not, Finset.mem_singleton,
      Subtype.ext_iff, σ, Equiv.Perm.subtypePerm_apply]
    exact ⟨fun h => fix_zero hadd ho h, fun h => by rw [h, g_zero hadd]⟩
  rw [hsupp, Fintype.card_coe] at hmod
  have hdvd := card_dvd16 S h0S hxS
  have h1S : (pt 1) ∈ S := (memS _).2 ⟨1, by norm_num, by
    change pt (cmb 1 a b c 1) = pt 1
    rw [cmb_one]⟩
  have hge : 2 ≤ S.card := Finset.one_lt_card.2 ⟨0, h0S, pt 1, h1S, by decide⟩
  have hcard : S.card = 16 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (show S.card ∣ 2 ^ 4 from hdvd)
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [hk'] at hge
      exact absurd hge (by decide)
    · rw [hk'] at hmod
      exact absurd hmod (by decide)
    · rw [hk'] at hmod
      exact absurd hmod (by decide)
    · rw [hk'] at hmod
      exact absurd hmod (by decide)
    · exact hk'
  have hinjOn := (Finset.card_image_iff (s := (Finset.univ : Finset (Fin 16)))
    (f := fun m : Fin 16 => pt (P m.val))).1 (by rw [hcard]; rfl)
  have hinj : ∀ m < 16, ∀ m' < 16, P m = P m' → m = m' := by
    intro m hm m' hm' e
    have := hinjOn (Finset.mem_coe.2 (Finset.mem_univ ⟨m, hm⟩))
      (Finset.mem_coe.2 (Finset.mem_univ ⟨m', hm'⟩)) (by simp only [e])
    exact congrArg Fin.val this
  have hsurj : ∀ i < 16, ∃ m < 16, P m = i := by
    intro i hi
    have hu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hcard]; rfl)
    obtain ⟨m, hm, e⟩ := (memS (pt i)).1 (hu ▸ Finset.mem_univ _)
    exact ⟨m, hm, pt_inj (hP16 m) hi e⟩
  refine ⟨a, b, c, Nat.pos_of_ne_zero fun e => hA0 (Fin.ext e), ha,
    Nat.pos_of_ne_zero fun e => hB0 (Fin.ext e), hb, Nat.pos_of_ne_zero fun e => hC0 (Fin.ext e),
    hc, ?_, ?_⟩
  ·
    unfold indep
    rw [CFSG.KS.Raw.Orb.allN_iff]
    intro m hm
    cases h : Nat.beq (cmb 1 a b c (Nat.succ m)) 0
    · rfl
    · exfalso
      have e : cmb 1 a b c (m + 1) = cmb 1 a b c 0 := by
        rw [cmb_zero]
        exact Nat.eq_of_beq_eq_true h
      have := hinj (m + 1) (by omega) 0 (by norm_num) e
      omega
  ·
    let Q : Nat → Nat := fun i => if h : i < 16 then Classical.choose (hsurj i h) else 0
    have hQ : ∀ i < 16, Q i < 16 ∧ P (Q i) = i := fun i hi => by
      simp only [Q, dif_pos hi]
      exact Classical.choose_spec (hsurj i hi)
    have hPQ : ∀ m < 16, P m < 16 ∧ Q (P m) = m := fun m hm =>
      ⟨hP16 m, hinj _ (hQ _ (hP16 m)).1 m hm (hQ _ (hP16 m)).2⟩
    have hF := fld_tabR P V Q hPQ hQ hV16 16 le_rfl
    have et : tab a b c = Nat.rec (motive := fun _ => Nat) 0
        (fun m ih => Nat.add ih (Nat.shiftLeft (V m) (Nat.mul 4 (P m)))) 16 := rfl
    refine ⟨?_, fun p => ?_⟩
    · rw [et]
      exact CFSG.KS.PF.shr_zero_of_fld (by norm_num) hF (fun i hi => by
        have : ¬ (i < 16 ∧ Q i < 16) := fun h => by omega
        rw [if_neg this])
    have hc : p.val < 16 ∧ Q p.val < 16 := ⟨p.isLt, (hQ p.val p.isLt).1⟩
    have e := CFSG.KS.PF.pg_of_fld (i := p.val) hF (by
      rw [if_pos hc]
      exact hV16 _)
    rw [if_pos hc] at e
    rw [et, e]
    have ep : pt (P (Q p.val)) = p := by rw [(hQ p.val p.isLt).2, pt_fin]
    have hg : g (pt (P (Q p.val))) = pt (V (Q p.val)) := by rw [g_pt, gP]
    rw [ep] at hg
    rw [hg, pt_val (hV16 _)]

end Order

noncomputable def ttP (s : Nat) : Equiv.Perm (Fin 16) :=
  if s = 0 then 1 else if s = 1 then tabPerm16 (tbarTabs[0]!) else
    if s = 2 then tabPerm16 (tbarTabs[1]!) else tabPerm16 (tbarTabs[0]!) * tabPerm16 (tbarTabs[1]!)

theorem ttP_mem (s : Nat) : ttP s ∈ Tbar16 := by
  have h0 : tabPerm16 (tbarTabs[0]!) ∈ Tbar16 := by
    unfold Tbar16
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  have h1 : tabPerm16 (tbarTabs[1]!) ∈ Tbar16 := by
    unfold Tbar16
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  unfold ttP
  split_ifs
  · exact Subgroup.one_mem _
  · exact h0
  · exact h1
  · exact Subgroup.mul_mem _ h0 h1

theorem tt_ap {s : Nat} (hs : s < 4) (p : Fin 16) : pg4 (TT s) p = (ttP s p).val := by
  interval_cases s
  · have e : ∀ q : Fin 16, pg4 (TT 0) q = q := by decide +kernel
    rw [e]
    unfold ttP
    rw [if_pos rfl]
    rfl
  · have e : ∀ q : Fin 16, pg4 (TT 1) q = pg4 (TB 0) q := by decide +kernel
    rw [e, tb_tab (j := 0) (by norm_num)]
    unfold ttP
    rw [if_neg (by norm_num), if_pos rfl]
  · have e : ∀ q : Fin 16, pg4 (TT 2) q = pg4 (TB 1) q := by decide +kernel
    rw [e, tb_tab (j := 1) (by norm_num)]
    unfold ttP
    rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
  · have e : ∀ q : Fin 16, pg4 (TT 3) q = pg4 (TB 0) (pg4 (TB 1) q) := by decide +kernel
    rw [e, tb_tab (j := 1) (by norm_num), tb_tab (j := 0) (by norm_num)]
    unfold ttP
    rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), Equiv.Perm.mul_apply]

theorem pw_tb {T : Nat} {x : Equiv.Perm (Fin 16)} (hT : ∀ p : Fin 16, pg4 T p = x p) (e : Nat)
    (p : Fin 16) : pw T e p = ((x ^ e) p).val := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have h : pw T (e + 1) p = pg4 T (pw T e p) := rfl
    rw [h, ih, hT, pow_succ', Equiv.Perm.mul_apply]

noncomputable def wE (g : Equiv.Perm (Fin 16)) (w : Nat) : Equiv.Perm (Fin 16) :=
  ttP (w % 4) * g ^ (w / 4 % 5) * ttP (w / 20)

theorem img_eq {T : Nat} {g : Equiv.Perm (Fin 16)} (hT : ∀ p : Fin 16, pg4 T p = g p) {w : Nat}
    (hw : w < 80) (p : Fin 16) : img T w p = (wE g w p).val := by
  have e : img T w p = pg4 (TT (w % 4)) (pw T (w / 4 % 5) (pg4 (TT (w / 20)) p)) := rfl
  rw [e, tt_ap (s := w / 20) (by omega) p, pw_tb hT, tt_ap (s := w % 4) (by omega)]
  unfold wE
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

noncomputable def kf (x : Equiv.Perm (Fin 16)) : Nat :=
  Nat.add (x 1).val (Nat.add (Nat.shiftLeft (x 2).val 4) (Nat.shiftLeft (x 4).val 8))

theorem key_eq {T : Nat} {g : Equiv.Perm (Fin 16)} (hT : ∀ p : Fin 16, pg4 T p = g p) {w : Nat}
    (hw : w < 80) : key T w = kf (wE g w) := by
  have e1 : img T w 1 = (wE g w 1).val := img_eq hT hw 1
  have e2 : img T w 2 = (wE g w 2).val := img_eq hT hw 2
  have e4 : img T w 4 = (wE g w 4).val := img_eq hT hw 4
  unfold key kf
  rw [e1, e2, e4]

theorem st_inv (κ : Nat → Nat) : ∀ k ≤ 80, ∃ c M : Nat,
    Nat.rec (motive := fun _ => Nat) 0 (fun w ih => strictN ih (fun st => addK st (κ w))) k =
      c + 256 * M ∧ c ≤ k ∧ c ≤ ((Finset.range k).image κ).card ∧
        ∀ w < k, M.testBit (κ w) = true := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨0, 0, rfl, le_rfl, by simp, fun w hw => absurd hw (Nat.not_lt_zero w)⟩
  | succ k ih =>
    intro hk
    obtain ⟨c, M, he, hck, hcS, hM⟩ := ih (by omega)
    have e : Nat.rec (motive := fun _ => Nat) 0 (fun w ih => strictN ih (fun st => addK st (κ w)))
        (k + 1) = addK (c + 256 * M) (κ k) := by
      change strictN (Nat.rec (motive := fun _ => Nat) 0
        (fun w ih => strictN ih (fun st => addK st (κ w))) k) (fun st => addK st (κ k)) = _
      rw [CFSG.KS.Raw.Orb.strictN_eq, he]
    rw [e]
    have hbit : bt (c + 256 * M) (Nat.add (κ k) 8) = M.testBit (κ k) := by
      rw [bt_eq]
      have e1 : c + 256 * M = 2 ^ 8 * M + c := by ring
      have h := Nat.testBit_two_pow_mul_add M (b := c) (i := 8) (by norm_num; omega) (κ k + 8)
      rw [if_neg (by omega), Nat.add_sub_cancel] at h
      rw [e1]
      exact h
    have hsub : (Finset.range k).image κ ⊆ (Finset.range (k + 1)).image κ :=
      Finset.image_subset_image (Finset.range_subset_range.2 (by omega))
    unfold addK
    rw [nIf_ite, hbit]
    by_cases hb : M.testBit (κ k) = true
    · rw [if_pos hb]
      refine ⟨c, M, rfl, by omega, le_trans hcS (Finset.card_le_card hsub), fun w hw => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hw with h | h
      · exact hM w h
      · rw [h]
        exact hb
    · rw [if_neg hb]
      have hb' : M.testBit (κ k) = false := by simpa using hb
      have hnot : κ k ∉ (Finset.range k).image κ := by
        intro hm
        obtain ⟨w, hw, e'⟩ := Finset.mem_image.1 hm
        rw [← e', hM w (Finset.mem_range.1 hw)] at hb'
        exact Bool.noConfusion hb'
      have hcard : ((Finset.range (k + 1)).image κ).card =
          ((Finset.range k).image κ).card + 1 := by
        rw [Finset.range_add_one, Finset.image_insert, Finset.card_insert_of_notMem hnot]
      have hor : M + 2 ^ κ k = M ||| 2 ^ κ k := testBit_add_disj (fun j => by
        rw [Nat.testBit_two_pow]
        by_cases hj : κ k = j
        · left
          rw [← hj]
          exact hb'
        · right
          simp [hj])
      have e2 : Nat.shiftLeft 1 (Nat.add (κ k) 8) = 256 * 2 ^ κ k := by
        rw [CFSG.KS.PF.shl_eq]
        change 1 * 2 ^ (κ k + 8) = _
        rw [Nat.pow_add]
        ring
      refine ⟨c + 1, M + 2 ^ κ k, ?_, by omega, by omega, fun w hw => ?_⟩
      · rw [e2]
        change c + 256 * M + (1 + 256 * 2 ^ κ k) = _
        ring
      · rw [hor, Nat.testBit_or, Nat.testBit_two_pow]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw with h | h
        · rw [hM w h]
          rfl
        · rw [h]
          simp

theorem famCnt_le (T : Nat) : famCnt T ≤ ((Finset.range 80).image (key T)).card := by
  obtain ⟨c, M, he, hc, hcS, -⟩ := st_inv (key T) 80 le_rfl
  have e : famCnt T = Nat.land (c + 256 * M) 255 := by
    unfold famCnt
    rw [he]
  rw [e]
  have h2 : Nat.land (c + 256 * M) 255 = (c + 256 * M) % 2 ^ 8 :=
    Nat.and_two_pow_sub_one_eq_mod _ 8
  have h3 : (c + 256 * M) % 2 ^ 8 = c := by
    rw [show (2 : Nat) ^ 8 = 256 from rfl]
    omega
  rw [h2, h3]
  exact hcS

theorem card_lt {T : Nat} {g : Equiv.Perm (Fin 16)} (hT : ∀ p : Fin 16, pg4 T p = g p)
    (h : 60 < famCnt T) :
    60 < Nat.card (Subgroup.closure ((Tbar16 : Set (Equiv.Perm (Fin 16))) ∪ {g})) := by
  set C := Subgroup.closure ((Tbar16 : Set (Equiv.Perm (Fin 16))) ∪ {g})
  have hmem : ∀ w, wE g w ∈ C := fun w => by
    have hg : g ∈ C := Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton g))
    have ht : ∀ s, ttP s ∈ C := fun s => Subgroup.subset_closure (Set.mem_union_left _ (ttP_mem s))
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ht _) (Subgroup.pow_mem _ hg _)) (ht _)
  have h1 : (Finset.range 80).image (key T) = ((Finset.range 80).image (wE g)).image kf := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun w hw => key_eq hT (Finset.mem_range.1 hw))
  have h2 := famCnt_le T
  rw [h1] at h2
  have h3 := Finset.card_image_le (s := (Finset.range 80).image (wE g)) (f := kf)
  have hsub : (((Finset.range 80).image (wE g) : Finset (Equiv.Perm (Fin 16))) :
      Set (Equiv.Perm (Fin 16))) ⊆ (C : Set (Equiv.Perm (Fin 16))) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hx
    exact hmem w
  have h4 : ((Finset.range 80).image (wE g)).card ≤ Nat.card C :=
    calc ((Finset.range 80).image (wE g)).card
        = Nat.card (((Finset.range 80).image (wE g) : Finset (Equiv.Perm (Fin 16))) :
          Set (Equiv.Perm (Fin 16))) := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ Nat.card (C : Set (Equiv.Perm (Fin 16))) := Nat.card_mono (Set.toFinite _) hsub
  omega

theorem mem_of_memK {X : Subgroup (Equiv.Perm (Fin 16))} {K : Nat → Nat} (R : Rec X K) {T : Nat}
    {g : Equiv.Perm (Fin 16)} (hT : ∀ p : Fin 16, pg4 T p = g p) (hm : memK K 60 T = true) :
    g ∈ X := by
  unfold memK at hm
  rw [Bool.not_eq_true', ← Bool.not_eq_true, CFSG.KS.Raw.Orb.allN_iff] at hm
  push Not at hm
  obtain ⟨s, hs, hk⟩ := hm
  have hk' : el K s = T := by
    cases h : Nat.beq (btKey 64 (mask 64) K s) T
    · rw [h] at hk
      exact absurd rfl hk
    · exact Nat.eq_of_beq_eq_true h
  have e : elt R s = g := elt_of R hs fun p => by rw [hk', hT p]
  rw [← e]
  exact elt_mem R hs

theorem inX_mem {T : Nat} {g : Equiv.Perm (Fin 16)} (hT : ∀ p : Fin 16, pg4 T p = g p)
    (h : inX T = true) :
    ∃ i < 4, g ∈ X16 i := by
  unfold inX at h
  cases h0 : memK SuzBtX0.K 60 T
  · cases h1 : memK SuzBtX1.K 60 T
    · cases h2 : memK SuzBtX2.K 60 T
      · cases h3 : memK SuzBtX3.K 60 T
        · rw [h0, h1, h2, h3] at h
          exact absurd h (by decide)
        · exact ⟨3, by norm_num, mem_of_memK rec3 hT h3⟩
      · exact ⟨2, by norm_num, mem_of_memK rec2 hT h2⟩
    · exact ⟨1, by norm_num, mem_of_memK rec1 hT h1⟩
  · exact ⟨0, by norm_num, mem_of_memK rec0 hT h0⟩

theorem chkA_all {a : Nat} (h0 : 0 < a) (h16 : a < 16) : chkA 60 inX a = true := by
  interval_cases a
  · exact kY1
  · exact kY2
  · exact kY3
  · exact kY4
  · exact kY5
  · exact kY6
  · exact kY7
  · exact kY8
  · exact kY9
  · exact kY10
  · exact kY11
  · exact kY12
  · exact kY13
  · exact kY14
  · exact kY15

theorem chk_of {a b c : Nat} (ha : 0 < a) (ha' : a < 16) (hb : 0 < b) (hb' : b < 16)
    (hc : 0 < c) (hc' : c < 16) (hi : indep a b c = true) :
    Nat.blt 60 (famCnt (tab a b c)) = true ∨ inX (tab a b c) = true := by
  have h := chkA_all ha ha'
  unfold chkA at h
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h (b - 1) (by omega)
  have h2 := CFSG.KS.Raw.Orb.allN_iff.1 h1 (c - 1) (by omega)
  have eb : Nat.succ (b - 1) = b := by omega
  have ec : Nat.succ (c - 1) = c := by omega
  beta_reduce at h2
  rw [eb, ec, CFSG.KS.Raw.Orb.bIf_eq, if_pos hi, CFSG.KS.Raw.Orb.strictB_eq] at h2
  beta_reduce at h2
  rw [CFSG.KS.Raw.Orb.bIf_eq] at h2
  by_cases hf : Nat.blt 60 (famCnt (tab a b c)) = true
  · exact Or.inl hf
  · rw [if_neg hf] at h2
    exact Or.inr h2

theorem part2 : ∀ g : Equiv.Perm (Fin 16),
    (∀ a b : Fin 16, g (xor16 a b) = xor16 (g a) (g b)) → orderOf g = 5 →
      (∃ i < 4, g ∈ X16 i) ∨
        60 < Nat.card (Subgroup.closure ((Tbar16 : Set (Equiv.Perm (Fin 16))) ∪ {g})) := by
  intro g hadd ho
  obtain ⟨a, b, c, ha, ha', hb, hb', hc, hc', hi, -, hT⟩ := alg hadd ho
  rcases chk_of ha ha' hb hb' hc hc' hi with h | h
  · exact Or.inr (card_lt hT (Nat.blt_eq.mp h))
  · exact Or.inl (inX_mem hT h)

theorem f9Prop : F9Prop := by
  unfold F9Prop
  exact ⟨f9Part1, part2⟩

end CertificateChecks.KernelSpor.SuzBtYG

end

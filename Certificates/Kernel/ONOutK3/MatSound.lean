module

public import Certificates.Kernel.ONOutK3.MatDefs
public import Certificates.Data.GrSLitL34FactsCF23ONOutK3Data
public import Certificates.Data.Kernel.ONOutK3.F
import Certificates.Kernel.Sporadic.ON8.Lin
import Certificates.Kernel.ONOutK3.Strong
import CFSG.Certificates.Kernel.Spor.Mat3Sound
import CFSG.Certificates.Kernel.Spor.PWord
import CFSG.Certificates.Kernel.ONOutK3.WalkSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.ONK3

open CFSG.KC.Enum CFSG.KC.ONK3 CFSG.ComponentClassification.SolMax.ONOut

open CFSG.KC.Ord CFSG.KS.Mat3 CFSG.KS.ONLin CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.Sporadic.ON.Native (nPts)
open scoped Matrix

local notation "MM" => mat3 154 23716

private def Rep (X : Nat) (f : Nat → Nat) : Prop :=
  Canon3 23716 X ∧ ∀ i < 245520, f i < 245520 ∧ vz (KK (f i)) = (MM X)ᵀ *ᵥ vz (KK i)

private theorem orbitK : Orbit 245520 KK := CertificateChecks.KernelSpor.ON8.orbit

private theorem rep_congr {X : Nat} {f g : Nat → Nat} (h : Rep X f) (e : ∀ i < 245520, f i = g i) :
    Rep X g :=
  ⟨h.1, fun i hi => by rw [← e i hi]; exact h.2 i hi⟩

section Consts

variable (hc : consts3OK 154 9 23716 LO RM CI ONE UP = true)
include hc

private theorem mul_eq {A B : Nat} (hA : Canon3 23716 A) (hB : Canon3 23716 B) :
    Canon3 23716 (MUL A B) ∧ MM (MUL A B) = MM A * MM B :=
  mul3s_sound hc hA hB

private theorem rep_mul {A B : Nat} {f g : Nat → Nat} (hA : Rep A f) (hB : Rep B g) :
    Rep (MUL A B) fun x => g (f x) := by
  obtain ⟨h1, h2⟩ := mul_eq hc hA.1 hB.1
  refine ⟨h1, fun i hi => ⟨(hB.2 _ (hA.2 i hi).1).1, ?_⟩⟩
  rw [(hB.2 _ (hA.2 i hi).1).2, (hA.2 i hi).2, Matrix.mulVec_mulVec, h2, Matrix.transpose_mul]

private theorem rep_one : Rep ONE fun x => x := by
  obtain ⟨h1, h2⟩ := one3_sound hc
  exact ⟨h1, fun i hi => ⟨hi, by rw [h2, Matrix.transpose_one, Matrix.one_mulVec]⟩⟩

private theorem rep_inv {A B : Nat} {f g : Nat → Nat} (hA : Rep A f) (hB : Canon3 23716 B)
    (hAB : MUL A B = ONE) (hg : ∀ i < 245520, g i < 245520 ∧ f (g i) = i) : Rep B g := by
  have e : MM A * MM B = 1 := by
    rw [← (mul_eq hc hA.1 hB).2, hAB, (one3_sound hc).2]
  refine ⟨hB, fun i hi => ⟨(hg i hi).1, ?_⟩⟩
  have h := (hA.2 _ (hg i hi).1).2
  rw [(hg i hi).2] at h
  rw [h, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.one_mulVec]

end Consts

section RowsK

open CFSG.KS.ON (canon vP vM canon_bits)

private noncomputable def Rk (F : Nat → Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => strictN acc fun a => strictN (F t) fun X =>
      Nat.lor a (Nat.lor (Nat.shiftLeft (Nat.land X M256) (Nat.mul (nat_lit 154) t))
        (Nat.shiftLeft (Nat.shiftRight X (nat_lit 256)) (Nat.add (nat_lit 23716) (Nat.mul (nat_lit 154) t)))))
    k

private theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

private theorem rowsK_eq (F : Nat → Nat) : rowsK F = Rk F 154 := rfl

private theorem M256_eq : M256 = 2 ^ 256 - 1 := pow_sub_one_eq 256

private theorem Rk_zero (F : Nat → Nat) : Rk F 0 = 0 := rfl

private theorem Rk_succ (F : Nat → Nat) (k : Nat) :
    Rk F (k + 1) = Rk F k ||| (vP (F k) <<< (154 * k) ||| vM (F k) <<< (23716 + 154 * k)) := by
  have h : Rk F (k + 1) = strictN (Rk F k) fun a => strictN (F k) fun X =>
      Nat.lor a (Nat.lor (Nat.shiftLeft (Nat.land X M256) (Nat.mul (nat_lit 154) k))
        (Nat.shiftLeft (Nat.shiftRight X (nat_lit 256))
          (Nat.add (nat_lit 23716) (Nat.mul (nat_lit 154) k)))) := rfl
  rw [h, strictN_eq', strictN_eq']
  rw [lor_eq3, lor_eq3, shl_eq3, shl_eq3, land_eq3, shr_eq3, M256_eq]
  rfl

private theorem big {Z : Nat} (h : Z < 2 ^ 154) {i : Nat} (hi : 154 ≤ i) : Z.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))

private theorem Rk_inv {F : Nat → Nat} (hF : ∀ t < 154, canon (F t) = true) :
    ∀ k ≤ 154, (∀ u, 2 * 23716 ≤ u → (Rk F k).testBit u = false) ∧
      (∀ t < 154, ∀ j < 154, (Rk F k).testBit (154 * t + j) = (decide (t < k) && (vP (F t)).testBit j)) ∧
      (∀ t < 154, ∀ j < 154,
        (Rk F k).testBit (23716 + (154 * t + j)) = (decide (t < k) && (vM (F t)).testBit j)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun u _ => ?_, fun t _ j _ => ?_, fun t _ j _ => ?_⟩ <;> simp [Rk_zero]
  | succ k ih =>
    intro hk
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    obtain ⟨-, hQ, hW⟩ := canon_bits (hF k (by omega))
    refine ⟨fun u hu => ?_, fun t ht j hj => ?_, fun t ht j hj => ?_⟩
    · rw [Rk_succ, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, h1 u hu]
      have a1 : (vP (F k)).testBit (u - 154 * k) = false := big hQ (by omega)
      have a2 : (vM (F k)).testBit (u - (23716 + 154 * k)) = false := big hW (by omega)
      simp [a1, a2]
    · rw [Rk_succ, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, h2 t ht j hj]
      have a2 : decide (23716 + 154 * k ≤ 154 * t + j) = false := by
        simp only [decide_eq_false_iff_not]; omega
      rw [a2]
      rcases lt_trichotomy t k with h | h | h
      · have a1 : decide (154 * k ≤ 154 * t + j) = false := by
          simp only [decide_eq_false_iff_not]; omega
        simp [a1, h, show t < k + 1 by omega]
      · subst h
        have e : 154 * t + j - 154 * t = j := by omega
        simp [e]
      · have a1 : (vP (F k)).testBit (154 * t + j - 154 * k) = false := big hQ (by omega)
        simp [a1, show ¬ t < k by omega, show ¬ t < k + 1 by omega]
    · rw [Rk_succ, Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, h3 t ht j hj]
      rcases lt_trichotomy t k with h | h | h
      · have a1 : decide (154 * k ≤ 23716 + (154 * t + j)) = true := by
          simp only [decide_eq_true_eq]; omega
        have a0 : (vP (F k)).testBit (23716 + (154 * t + j) - 154 * k) = false := big hQ (by omega)
        have a2 : decide (23716 + 154 * k ≤ 23716 + (154 * t + j)) = false := by
          simp only [decide_eq_false_iff_not]; omega
        rw [a2]
        simp [a0, h, show t < k + 1 by omega]
      · subst h
        have e : 23716 + (154 * t + j) - (23716 + 154 * t) = j := by omega
        have a0 : (vP (F t)).testBit (23716 + (154 * t + j) - 154 * t) = false := big hQ (by omega)
        simp [e, a0]
      · have a0 : (vP (F k)).testBit (23716 + (154 * t + j) - 154 * k) = false := big hQ (by omega)
        have a1 : (vM (F k)).testBit (23716 + (154 * t + j) - (23716 + 154 * k)) = false :=
          big hW (by omega)
        simp [a0, a1, show ¬ t < k by omega, show ¬ t < k + 1 by omega]

private theorem rowsK_bits {F : Nat → Nat} (hF : ∀ t < 154, canon (F t) = true) :
    Canon3 23716 (rowsK F) ∧ ∀ t < 154, ∀ j < 154,
      (rowsK F).testBit (154 * t + j) = (vP (F t)).testBit j ∧
      (rowsK F).testBit (23716 + (154 * t + j)) = (vM (F t)).testBit j := by
  rw [rowsK_eq]
  obtain ⟨h1, h2, h3⟩ := Rk_inv hF 154 le_rfl
  have hlt : ∀ t < 154, ∀ j < 154, (Rk F 154).testBit (154 * t + j) = (vP (F t)).testBit j ∧
      (Rk F 154).testBit (23716 + (154 * t + j)) = (vM (F t)).testBit j := fun t ht j hj => by
    rw [h2 t ht j hj, h3 t ht j hj]; simp [ht]
  refine ⟨⟨?_, fun u hu => ?_⟩, hlt⟩
  · apply Nat.lt_pow_two_of_testBit
    intro i hi
    exact h1 i (by omega)
  · by_cases hu2 : u < 23716
    · obtain ⟨-, hd, -⟩ := canon_bits (hF (u / 154) (by omega))
      have hq := hlt (u / 154) (by omega) (u % 154) (Nat.mod_lt _ (by omega))
      have e : 154 * (u / 154) + u % 154 = u := Nat.div_add_mod u 154
      rw [e] at hq
      have hb : vP (F (u / 154)) &&& vM (F (u / 154)) = 0 := (canon_bits (hF (u / 154) (by omega))).1
      rw [hq.2]
      rw [hq.1] at hu
      have := congrArg (fun z => z.testBit (u % 154)) hb
      simp only [Nat.testBit_and, Nat.zero_testBit] at this
      rw [hu] at this
      simpa using this
    · rw [h1 _ (by omega)]

end RowsK

private theorem rowsK_mat {F : Nat → Nat} (hF : ∀ t < 154, CFSG.KS.ON.canon (F t) = true) :
    Canon3 23716 (rowsK F) ∧ ∀ t j : Fin 154, MM (rowsK F) t j = vz (F t) j := by
  obtain ⟨h1, h2⟩ := rowsK_bits hF
  refine ⟨h1, fun t j => ?_⟩
  obtain ⟨e1, e2⟩ := h2 t t.isLt j j.isLt
  change bv _ _ = (CFSG.KS.ON.vOf (F t)).val j.val
  rw [e1, e2, CFSG.F3.Native.V.val_eq_bitVal]
  rfl

private theorem rep_matT (hc : consts3OK 154 9 23716 LO RM CI ONE UP = true) {PI : Nat}
    (hPI : Canon3 23716 PI) (h2 : MUL (rowsK fun t => KK (SPf t)) PI = ONE) {f : Nat → Nat}
    (hf : Lin 245520 KK f) : Rep (matT KK SPf PI f) f := by
  obtain ⟨M, hM⟩ := hf
  have hsp : ∀ t < 154, SPf t < 245520 := CertificateChecks.KernelSpor.ON8.spans'.1
  obtain ⟨cS, eS⟩ := rowsK_mat fun t ht => orbitK.1 _ (hsp t ht)
  obtain ⟨cF, eF⟩ := rowsK_mat (F := fun t => KK (f (SPf t))) fun t ht =>
    orbitK.1 _ (hM _ (hsp t ht)).1
  have e1 : MM PI * MM (rowsK fun t => KK (SPf t)) = 1 := by
    rw [mul_eq_one_comm, ← (mul_eq hc cS hPI).2, h2, (one3_sound hc).2]
  have e2 : MM (rowsK fun t => KK (f (SPf t))) = MM (rowsK fun t => KK (SPf t)) * Mᵀ := by
    ext t j
    rw [eF t j, Matrix.mul_apply]
    rw [(hM _ (hsp t t.isLt)).2]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, eS]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have e3 : MM (matT KK SPf PI f) = Mᵀ := by
    rw [matT, (mul_eq hc hPI cF).2, e2, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  refine ⟨(mul_eq hc hPI cF).1, fun i hi => ⟨(hM i hi).1, ?_⟩⟩
  rw [e3, Matrix.transpose_transpose, (hM i hi).2]

private theorem rep_letter (hc : consts3OK 154 9 23716 LO RM CI ONE UP = true) {MT : Nat → Nat}
    {G GI : Nat → Nat → Nat} {m : Nat}
    (hl : ∀ h < m, Rep (MT (2 * h)) (G h) ∧ Rep (MT (2 * h + 1)) (GI h)) {l : Int}
    (hl0 : l ≠ 0 ∧ l.natAbs ≤ m) : Rep (MT (lcode l)) (CFSG.KS.TW.GZ G GI l) := by
  rcases l with k | k
  · have hk : k ≠ 0 := fun h => hl0.1 (by simp [h])
    have hkm : k ≤ m := by simpa using hl0.2
    have e : lcode (Int.ofNat k) = 2 * (k - 1) := by
      change Nat.mul 2 (Nat.pred k) = _
      rw [Nat.pred_eq_sub_one]
      rfl
    have eG : CFSG.KS.TW.GZ G GI (Int.ofNat k) = G (k - 1) := by
      funext y
      unfold CFSG.KS.TW.GZ
      rw [if_pos (by simp only [Int.ofNat_eq_coe]; omega)]
      rfl
    rw [e, eG]
    exact (hl (k - 1) (by omega)).1
  · have hkm : k + 1 ≤ m := by simpa using hl0.2
    have e : lcode (Int.negSucc k) = 2 * k + 1 := rfl
    have eG : CFSG.KS.TW.GZ G GI (Int.negSucc k) = GI k := by
      funext y
      unfold CFSG.KS.TW.GZ
      rw [if_neg (by simp [Int.negSucc_lt_zero, le_of_lt])]
      simp [Int.neg_negSucc]
    rw [e, eG]
    exact (hl k (by omega)).2

private theorem rep_wordT (hc : consts3OK 154 9 23716 LO RM CI ONE UP = true) {MT : Nat → Nat}
    {G GI : Nat → Nat → Nat} {m : Nat}
    (hl : ∀ h < m, Rep (MT (2 * h)) (G h) ∧ Rep (MT (2 * h + 1)) (GI h)) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m) →
      Rep (wordT MT w) fun x => w.foldr (CFSG.KS.TW.GZ G GI) x := by
  intro w
  induction w with
  | nil =>
    intro _
    rw [show wordT MT [] = ONE by rw [wordT, List.foldr_nil]]
    exact rep_one hc
  | cons l w ih =>
    intro hw
    have h1 := ih fun z hz => hw z (List.mem_cons_of_mem l hz)
    have h2 := rep_mul hc h1 (rep_letter hc hl (hw l List.mem_cons_self))
    have e : wordT MT (l :: w) = MUL (wordT MT w) (MT (lcode l)) := by
      show strictN (wordT MT w) (fun a => MUL a (MT (lcode l))) = _
      exact strictN_eq' _ _
    rw [e]
    exact h2

private theorem rep_uT (hc : consts3OK 154 9 23716 LO RM CI ONE UP = true) {HT : Nat → Nat}
    {G : Nat → Nat → Nat} (hl : ∀ a < 3, Rep (HT a) (G a)) :
    ∀ d w acc (f : Nat → Nat), CFSG.KS.ONK3.Lets d w → Rep acc f →
      Rep (uT HT d w acc) fun x => gword G d w (f x) := by
  intro d
  induction d with
  | zero => exact fun _ _ _ _ hacc => hacc
  | succ d ih =>
    intro w acc f hw hacc
    obtain ⟨hw', h3⟩ := hw.tail
    have e1 : uT HT (d + 1) w acc = uT HT d (w / 4) (MUL acc (HT (w % 4))) := by
      change strictN (MUL acc (HT (Nat.land w 3))) (fun a => uT HT d (Nat.shiftRight w 2) a) = _
      rw [strictN_eq', show Nat.land w 3 = w % 4 from Nat.and_two_pow_sub_one_eq_mod w 2,
        show Nat.shiftRight w 2 = w / 4 from Nat.shiftRight_eq_div_pow w 2]
    have e2 : (fun x => gword G (d + 1) w (f x)) = fun x => gword G d (w / 4) (G (w % 4) (f x)) :=
      funext fun x => CFSG.KS.ONK3.gword_succ G d w (f x)
    rw [e1, e2]
    exact ih (w / 4) _ _ hw' (rep_mul hc hacc (hl _ h3))

private theorem lets_of {j : Nat} {w : List Int} (h : CFSG.ONSchreier.Native.plettersOK j w = true) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ j := fun l hl => by
  have := List.all_eq_true.1 h l hl
  simpa using this

private theorem fin_apply_inv {x : Nat} (hx : x < 245520) (g : Equiv.Perm (Fin nPts)) :
    ((g (g⁻¹ ⟨x, hx⟩) : Fin nPts) : Nat) = x := by
  simp

private theorem sig_inv_get {j : Nat} (hj : j < 7) {x : Nat} (hx : x < 245520) :
    ((pinvs nPts sigStrong)[j]!)[x]! = ((permOfArr nPts sigStrong[j]!)⁻¹ ⟨x, hx⟩ : Nat) := by
  rw [sigInv_get hj]
  exact (prep_pinv (sig_size' hj) (sig_prep j hj)).apply hx

private theorem sig_get {j : Nat} (hj : j < 7) (y : Fin nPts) :
    (sigStrong[j]!)[(y : Nat)]! = ((permOfArr nPts sigStrong[j]!) y : Nat) :=
  (sig_prep j hj) y

private theorem sig_inv {j : Nat} (hj : j < 7) {x : Nat} (hx : x < 245520) :
    (sigStrong[j]!)[x]! < 245520 ∧ ((pinvs nPts sigStrong)[j]!)[x]! < 245520 ∧
      (sigStrong[j]!)[((pinvs nPts sigStrong)[j]!)[x]!]! = x := by
  refine ⟨(sig_prep j hj).lt hx, ?_, ?_⟩
  · rw [sigInv_get hj]
    exact (prep_pinv (sig_size' hj) (sig_prep j hj)).lt hx
  · rw [sig_inv_get hj hx, sig_get hj]
    exact fin_apply_inv hx _

private theorem sig_letters {m : Nat} (hm : m ≤ 7) :
    CFSG.KS.PW.LettersOK 245520 m sigStrong (pinvs nPts sigStrong)
      (fun j x => (sigStrong[j]!)[x]!) (fun j x => ((pinvs nPts sigStrong)[j]!)[x]!) :=
  fun j hj x hx => ⟨rfl, rfl, (sig_inv (by omega) hx).1, (sig_inv (by omega) hx).2.1⟩

theorem vArrs_of_mchk (MD : Nat → Nat) (h : ∀ c < 37, mchkG MD c = true) :
    ∀ l < 3, ∀ x < 245520,
      (vArrs[l]!)[x]! = gword CertificateChecks.KernelSpor.ON3.mG (UL l) (UW l) x := by
  have hc : consts3OK 154 9 23716 LO RM CI ONE UP = true := h 0 (by norm_num)
  have hV : ∀ i < 32, Canon3 23716 (MD i) := fun i hi => by
    have h1 : allN 32 (fun i => VLD (MD i)) = true := h 1 (by norm_num)
    exact (valid3_iff (consts3_facts hc).2.2.1).1 (CFSG.KS.allN_spec h1 i hi)
  have h2 : MUL (rowsK fun t => KK (SPf t)) (MD 0) = ONE := Nat.eq_of_beq_eq_true (h 2 (by norm_num))
  have hPI := hV 0 (by norm_num)
  have hT : ∀ i < 7, Rep (MD (1 + i)) (CertificateChecks.KernelSpor.ON.TT i) := fun i hi => by
    have e : mchkG MD (3 + i) =
        Nat.beq (MD (1 + i)) (matT KK SPf (MD 0) (CertificateChecks.KernelSpor.ON.TT i)) := by
      interval_cases i <;> rfl
    have := h (3 + i) (by omega)
    rw [e] at this
    rw [Nat.eq_of_beq_eq_true this]
    exact rep_matT hc hPI h2 (CertificateChecks.KernelSpor.ON8.lin_TT hi)
  have hU : ∀ i < 7, Rep (MD (8 + i)) (CertificateChecks.KernelSpor.ON.UU i) := fun i hi => by
    have e : mchkG MD (10 + i) =
        Nat.beq (MD (8 + i)) (matT KK SPf (MD 0) (CertificateChecks.KernelSpor.ON.UU i)) := by
      interval_cases i <;> rfl
    have := h (10 + i) (by omega)
    rw [e] at this
    rw [Nat.eq_of_beq_eq_true this]
    exact rep_matT hc hPI h2 (CertificateChecks.KernelSpor.ON8.lin_UU hi)
  have hG : ∀ a < 3, Rep (MD (29 + a)) (CertificateChecks.KernelSpor.ON3.mG a) := fun a ha => by
    have e : mchkG MD (17 + a) =
        Nat.beq (MD (29 + a)) (matT KK SPf (MD 0) (CertificateChecks.KernelSpor.ON3.mG a)) := by
      interval_cases a <;> rfl
    have := h (17 + a) (by omega)
    rw [e] at this
    rw [Nat.eq_of_beq_eq_true this]
    exact rep_matT hc hPI h2 (CertificateChecks.KernelSpor.ON8.lin_mG ha)
  have hsM : ∀ i < 7, Rep (sM MD (2 * i)) (CertificateChecks.KernelSpor.ON.TT i) ∧
      Rep (sM MD (2 * i + 1)) (CertificateChecks.KernelSpor.ON.UU i) := fun i hi => by
    have e1 : sM MD (2 * i) = MD (1 + i) := by interval_cases i <;> rfl
    have e2 : sM MD (2 * i + 1) = MD (8 + i) := by interval_cases i <;> rfl
    rw [e1, e2]
    exact ⟨hT i hi, hU i hi⟩
  have hgM : ∀ i < 7, gM MD (2 * i) = MD (15 + i) ∧ gM MD (2 * i + 1) = MD (22 + i) :=
    fun i hi => by constructor <;> interval_cases i <;> rfl
  have hsig : ∀ j < 7, Rep (MD (15 + j)) (fun x => (sigStrong[j]!)[x]!) ∧
      Rep (MD (22 + j)) (fun x => ((pinvs nPts sigStrong)[j]!)[x]!) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hj
    have hfw : Rep (MD (15 + j)) (fun x => (sigStrong[j]!)[x]!) := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2j
      · have e : MD 15 = wordT (sM MD) wA := Nat.eq_of_beq_eq_true (h 20 (by norm_num))
        have hl := lets_of wA_letters
        rw [show 15 + 0 = 15 from rfl, e]
        refine rep_congr (rep_wordT hc hsM wA hl) fun x hx => ?_
        rw [show sigStrong[0]! = wordArr wA from sig_facts.2.1]
        exact (CFSG.KS.PW.pword_get CertificateChecks.KernelSpor.ON3.qon_letters wA hl x hx).1.symm
      · have e : MD 16 = wordT (sM MD) wB := Nat.eq_of_beq_eq_true (h 21 (by norm_num))
        have hl := lets_of wB_letters
        rw [show 15 + 1 = 16 from rfl, e]
        refine rep_congr (rep_wordT hc hsM wB hl) fun x hx => ?_
        rw [show sigStrong[1]! = wordArr wB from sig_facts.2.2.1]
        exact (CFSG.KS.PW.pword_get CertificateChecks.KernelSpor.ON3.qon_letters wB hl x hx).1.symm
      · have e : mchkG MD (20 + j) =
            Nat.beq (MD (15 + j)) (wordT (gM MD) CFSG.ONSchreier.Data.strongWords[j]!) := by
          interval_cases j <;> rfl
        have := h (20 + j) (by omega)
        rw [e] at this
        have hl := lets_of (W_letters j (by rw [W_size]; exact hj) h2j)
        have hr := rep_wordT hc (MT := gM MD) (G := fun i x => (sigStrong[i]!)[x]!) (GI := fun i x => ((pinvs nPts sigStrong)[i]!)[x]!) (m := j)
          (fun i hi => by
          rw [(hgM i (by omega)).1, (hgM i (by omega)).2]
          exact ih i hi (by omega)) _ hl
        rw [Nat.eq_of_beq_eq_true this]
        refine rep_congr hr fun x hx => ?_
        have hw : sigStrong[j]! =
            pword nPts sigStrong (pinvs nPts sigStrong) CFSG.ONSchreier.Data.strongWords[j]! :=
          sig_facts.2.2.2 j (by rw [W_size]; exact hj) h2j
        rw [hw]
        exact (CFSG.KS.PW.pword_get (sig_letters (by omega)) _ hl x hx).1.symm
    refine ⟨hfw, ?_⟩
    have e : mchkG MD (27 + j) = Nat.beq (MUL (MD (15 + j)) (MD (22 + j))) ONE := by
      interval_cases j <;> rfl
    have := h (27 + j) (by omega)
    rw [e] at this
    exact rep_inv hc hfw (hV _ (by omega)) (Nat.eq_of_beq_eq_true this) fun x hx =>
      ⟨(sig_inv hj hx).2.1, (sig_inv hj hx).2.2⟩
  intro l hl x hx
  have hMW : CFSG.ONSchreier.Native.plettersOK 7 CFSG.ONSchreier.Data.MWords[l]! = true := by
    interval_cases l <;> decide
  have r1 := rep_wordT hc (MT := gM MD) (G := fun i x => (sigStrong[i]!)[x]!) (GI := fun i x => ((pinvs nPts sigStrong)[i]!)[x]!) (m := 7)
    (fun i hi => by
    rw [(hgM i hi).1, (hgM i hi).2]
    exact hsig i hi) _ (lets_of hMW)
  have hLets : CFSG.KS.ONK3.Lets (UL l) (UW l) := by interval_cases l <;> rfl
  have r2 := rep_uT hc (HT := hM MD) hG (UL l) (UW l) ONE (fun x => x) hLets (rep_one hc)
  have e : mchkG MD (34 + l) =
      Nat.beq (wordT (gM MD) CFSG.ONSchreier.Data.MWords[l]!) (uT (hM MD) (UL l) (UW l) ONE) := by
    interval_cases l <;> rfl
  have := h (34 + l) (by omega)
  rw [e] at this
  rw [Nat.eq_of_beq_eq_true this] at r1
  have hx1 := r1.2 x hx
  have hx2 := r2.2 x hx
  have heq := orbitK.eq_of_vz hx1.1 hx2.1 (by rw [hx1.2, hx2.2])
  have hv : (vArrs[l]!)[x]! = CFSG.ONSchreier.Data.MWords[l]!.foldr
      (CFSG.KS.TW.GZ (fun j x => (sigStrong[j]!)[x]!) fun j x => ((pinvs nPts sigStrong)[j]!)[x]!) x := by
    unfold vArrs
    rw [CFSG.KS.PW.pwords_get (by interval_cases l <;> decide)]
    exact (CFSG.KS.PW.pword_get (sig_letters le_rfl) _ (lets_of hMW) x hx).1
  rw [hv]
  exact heq

end CertificateChecks.KernelSpor.ONK3

end

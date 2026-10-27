module

public import Certificates.Kernel.J2Cover.M22Lk
public import Certificates.Kernel.J2Cover.ModelsBind
public import Certificates.Kernel.J2Cover.K20D
public import CFSG.Certificates.Kernel.J2ModelsSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Kernel.J2Cover.M22Blocks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.DecText CFSG.KC.Misc.ArrEnum CFSG.KC.J2Models
open CFSG.ComponentClassification.J2Cover.Models

theorem pg_beyond {n w P i : Nat} (hP0 : Nat.beq (Nat.shiftRight P (n * w)) 0 = true)
    (h : n ≤ i) : pg w (mask w) P i = 0 := by
  have hP : P < 2 ^ (n * w) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  have hw : n * w ≤ w * i := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left w h
  have e : Nat.shiftRight P (Nat.mul w i) = 0 := by
    have e1 : Nat.shiftRight P (Nat.mul w i) = P >>> (w * i) := rfl
    rw [e1, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) hw))
  unfold pg
  rw [e]
  exact Nat.zero_and _

theorem blt_false {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff]
  intro h'
  exact h (Nat.le_of_ble_eq_true h')

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := Nat.ble_eq_true_of_le h

theorem beq_false {a : Nat} (h : a ≠ 0) : Nat.beq a 0 = false :=
  Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')

theorem fMT_all (a : Nat) (ha : a < 128) : fMT a = true :=
  CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) MTB.all a ha

theorem mt_pt (a d : Nat) : (mulTab[a]!)[d]! = mtK a d := by
  by_cases ha : a < 128
  · have h := fMT_all a ha
    unfold fMT at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    unfold mtK
    rw [blt_true ha]
    unfold mulTab
    rw [getElem!_ofFn' ha]
    by_cases hd : d < 128
    · rw [getElem!_ofFn' hd]
      exact Nat.eq_of_beq_eq_true (allN_spec h2 d hd)
    · rw [getElem!_neg _ d (by rw [Array.size_ofFn]; exact hd), pg_beyond h1 (by omega)]
      rfl
  · unfold mtK
    rw [blt_false ha]
    unfold mulTab
    rw [getElem!_neg _ a (by rw [Array.size_ofFn]; exact ha)]
    rfl

theorem mt_eq : (fun a d => (mulTab[a]!)[d]!) = mtK := funext fun a => funext fun d => mt_pt a d

theorem kCW0 : Nat.beq (Nat.shiftRight CW0P (4725 * 7)) 0 = true := by quickRfl
theorem kCW1 : Nat.beq (Nat.shiftRight CW1P (4725 * 7)) 0 = true := by quickRfl
theorem kCA0 : Nat.beq (Nat.shiftRight CA0P (4725 * 13)) 0 = true := by quickRfl
theorem kCA1 : Nat.beq (Nat.shiftRight CA1P (4725 * 13)) 0 = true := by quickRfl

theorem cosetWit0_eq : cosetWit0 = unpack 4725 7 CW0P := natsOf_bind NW0.eq (by quickRfl) (by quickRfl)
theorem cosetWit1_eq : cosetWit1 = unpack 4725 7 CW1P := natsOf_bind NW1.eq (by quickRfl) (by quickRfl)
theorem cosetAct0_eq : cosetAct0 = unpack 4725 13 CA0P := natsOf_bind NA0.eq (by quickRfl) (by quickRfl)
theorem cosetAct1_eq : cosetAct1 = unpack 4725 13 CA1P := natsOf_bind NA1.eq (by quickRfl) (by quickRfl)

theorem wit_pt (j i : Nat) : witT j i = witK j i := by
  unfold witT witK
  by_cases hj : j = 0
  · subst hj
    rw [ite_eq_left rfl, cosetWit0_eq, getElem!_unpack_all kCW0]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hj), cosetWit1_eq, getElem!_unpack_all kCW1,
      beq_false hj]

theorem act_pt (j i : Nat) : actT j i = actK j i := by
  unfold actT actK
  by_cases hj : j = 0
  · subst hj
    rw [ite_eq_left rfl, cosetAct0_eq, getElem!_unpack_all kCA0]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hj), cosetAct1_eq, getElem!_unpack_all kCA1,
      beq_false hj]

theorem kFR : Nat.beq (Nat.shiftRight FRP (128 * 128)) 0 = true := by quickRfl

theorem fRows_eqP : fRows = unpack 128 128 FRP :=
  natsOf_bind CertificateChecks.KernelLC.FR.eq (by quickRfl) (by quickRfl)

theorem fR_eq : (fun x => fRows[x]!) = fRK :=
  funext fun x => by rw [fRows_eqP, getElem!_unpack_all kFR]; rfl

theorem kHR : allN 6 (fun j => Nat.beq (Nat.shiftRight (HRP j) (128 * 128)) 0) = true := by quickRfl

theorem hRows_eqP (j : Nat) (hj : j < 6) : hRowsT j = unpack 128 128 (HRP j) := by
  interval_cases j
  · exact natsOf_bind NH0.eq (by quickRfl) (by quickRfl)
  · exact natsOf_bind NH1.eq (by quickRfl) (by quickRfl)
  · exact natsOf_bind NH2.eq (by quickRfl) (by quickRfl)
  · exact natsOf_bind NH3.eq (by quickRfl) (by quickRfl)
  · exact natsOf_bind NH4.eq (by quickRfl) (by quickRfl)
  · exact natsOf_bind NH5.eq (by quickRfl) (by quickRfl)

theorem hR_eq : (fun j x => (hRowsT j)[x]!) = hRK := by
  funext j x
  unfold hRK
  by_cases hj : j < 6
  · rw [blt_true hj, hRows_eqP j hj, getElem!_unpack_all (allN_spec kHR j hj)]
  · rw [blt_false hj]
    unfold hRowsT hRowsAll
    rw [getElem!_neg _ j (by simp; omega)]
    rfl

theorem yDecomp_pt (k i : Nat) (hk : k < 3) (hi : i < 4725) : yDecomp k i = yDK k i := by
  have hm : 4725 * k + i < 14175 := by omega
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) YDB.all (4725 * k + i) hm
  unfold fYD at h
  have e1 : Nat.div (4725 * k + i) 4725 = k := by
    change (4725 * k + i) / 4725 = k
    omega
  have e2 : Nat.mod (4725 * k + i) 4725 = i := by
    change (4725 * k + i) % 4725 = i
    omega
  rw [e1, e2] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have e : yDecomp k i = yFold k i := by
    unfold yDecomp yFold
    simp only [mt_pt, wit_pt, act_pt]
  rw [e]
  exact Prod.ext (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)

end CertificateChecks.KernelJ2Cover

end

module

public import Certificates.Kernel.Sporadic.Tits.Bind2264
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
meta import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelSporSch.TitsZ 11 CFSG.Sporadic.Schreier.Tits.titsZArr

namespace CertificateChecks.KernelSporSch.TitsCommon

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSporSch

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  simp only [unpack]
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem unpack_get0 {n w P i : Nat} (hP0 : Nat.beq (Nat.shiftRight P (n * w)) 0 = true) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  have hP : P < 2 ^ (n * w) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  by_cases h : i < n
  · exact unpack_get h
  · rw [getElem!_neg _ i (by unfold unpack; rw [Array.size_ofFn]; exact h)]
    have hw : n * w ≤ w * i := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left w (by omega)
    have e : Nat.shiftRight P (Nat.mul w i) = 0 := by
      have e1 : Nat.shiftRight P (Nat.mul w i) = P >>> (w * i) := rfl
      rw [e1, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by decide) hw))
    unfold pg
    rw [e]
    exact (Nat.zero_and _).symm

theorem canonD : allN 13 (fun j => bAnd(canonK 1755 11 (mask 11) (1755 * 11) (TitsD.S j),
    canonK 1755 11 (mask 11) (1755 * 11) (TitsD.SI j))) = true := by quickRfl

theorem canonS {j : Nat} (hj : j < 13) : canonK 1755 11 (mask 11) (1755 * 11) (TitsD.S j) = true :=
  ((bAnd_iff _ _).1 (allN_spec canonD j hj)).1

theorem canonSI {j : Nat} (hj : j < 13) :
    canonK 1755 11 (mask 11) (1755 * 11) (TitsD.SI j) = true :=
  ((bAnd_iff _ _).1 (allN_spec canonD j hj)).2

theorem derInv_eq {j : Nat} (hj : j < 13) :
    invCand 1755 titsDerivedArrs[j]! = unpack 1755 11 (TitsD.SI j) := by
  rw [der_eq hj]
  exact (invEqK_sound (allN_spec permD j hj)).1

theorem zW : wordEqK 1755 11 (mask 11) (pidn 1755 11) TitsD.S TitsD.SI 13 titsCenterWord TitsZ =
    true := by
  unfold wordEqK
  quickRfl

theorem z_eq : titsZArr = unpack 1755 11 TitsZ :=
  (wordEqK_sound ⟨bindsD.2.2.2.1, bindsD.2.2.2.2.1⟩ permD zW).1

theorem canonZ : canonK 1755 11 (mask 11) (1755 * 11) TitsZ = true := by quickRfl

end CertificateChecks.KernelSporSch.TitsCommon

end

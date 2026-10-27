module

public import Certificates.Kernel.J2Cover.ModelsBind
public import Certificates.Kernel.J2Cover.K20C
public import Certificates.Kernel.J2Cover.K20X
public import Certificates.Kernel.LocalComp.J2Disp
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.ComponentClassification.J2Cover.External (fusionP fusionI fusionArr lamCheck fusionBit)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem fusionP_eq : fusionP = unpack 4725 13 FPP := natsOf_bind NFP.eq (by quickRfl) (by quickRfl)

theorem fusionI_eq : fusionI = unpack 4725 13 FIP := natsOf_bind NFI.eq (by quickRfl) (by quickRfl)

theorem aCoefT_eq : aCoefT = unpack 4725 13 ACP := natsOf_bind NAC.eq (by quickRfl) (by quickRfl)

theorem cFU : CnN 315 9 FU := by quickRfl

theorem getElem!_unpack_all {n w P i : Nat} (hP0 : Nat.beq (Nat.shiftRight P (n * w)) 0 = true) :
    (unpack n w P)[i]! = pg w (mask w) P i := by
  have hP : P < 2 ^ (n * w) := Nat.lt_of_div_eq_zero (Nat.two_pow_pos _)
    (by rw [← Nat.shiftRight_eq_div_pow]; exact Nat.eq_of_beq_eq_true hP0)
  by_cases h : i < n
  · exact getElem!_unpack h
  · rw [getElem!_neg _ i (by unfold unpack; rw [Array.size_ofFn]; exact h)]
    have hw : n * w ≤ w * i := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left w (by omega)
    have e : Nat.shiftRight P (Nat.mul w i) = 0 := by
      have e1 : Nat.shiftRight P (Nat.mul w i) = P >>> (w * i) := rfl
      rw [e1, Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hP (Nat.pow_le_pow_right (by norm_num) hw))
    unfold pg
    rw [e]
    exact (Nat.zero_and _).symm

@[expose] noncomputable def lamTK (i : Nat) : Bool :=
  strictB (pg 13 (mask 13) FPP i) fun p => strictB (pg 13 (mask 13) FIP i) fun q =>
    bAnd(Nat.blt p 128, bAnd(Nat.blt q 4725,
      Nat.beq (pcomp 315 9 (mask 9) (RPT i) FU) (pcomp 315 9 (mask 9) (ELT p) (RPT q))))

#lc_blocks LMB lamTK 4725 32

theorem lamPart : allLt 4725 (fun i => decide (fusionP[i]! < 128) && decide (fusionI[i]! < 4725) &&
    eqA 315 (compA 315 repArrs[i]! fusionArr)
      (compA 315 eltArrs[fusionP[i]!]! repArrs[fusionI[i]!]!)) = true := by
  refine allLt_iff.2 fun i hi => ?_
  have h := CFSG.KC.Co3Bfs.cover_of_blocks (by norm_num) (by norm_num) LMB.all i hi
  unfold lamTK at h
  rw [strictB_eq', strictB_eq'] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  have hp := Nat.le_of_ble_eq_true h1
  have hq := Nat.le_of_ble_eq_true h2
  rw [fusionP_eq, fusionI_eq, getElem!_unpack hi, getElem!_unpack hi, repArrs_eq i hi, hFU,
    eltArrs_eq _ hp, repArrs_eq _ hq, compA_unpackN (repT_canon i hi) cFU,
    compA_unpackN (eltT_canon _ hp) (repT_canon _ hq),
    eqA_unpackN (canon_pcN (repT_canon i hi) cFU) (canon_pcN (eltT_canon _ hp) (repT_canon _ hq)), h3]
  simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hp, hq⟩

theorem kFPP : Nat.beq (Nat.shiftRight FPP (4725 * 13)) 0 = true := by quickRfl

theorem kFIP : Nat.beq (Nat.shiftRight FIP (4725 * 13)) 0 = true := by quickRfl

theorem kACP : Nat.beq (Nat.shiftRight ACP (4725 * 13)) 0 = true := by quickRfl

theorem getElem!_ofFn_all {α : Type} [Inhabited α] {n : Nat} {f : Fin n → α} {i : Nat} :
    (Array.ofFn f)[i]! = if h : i < n then f ⟨i, h⟩ else default := by
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    exact getElem!_ofFn' h
  · simp only [h, ↓reduceDIte]
    exact getElem!_neg _ i (by rw [Array.size_ofFn]; exact h)

theorem fusionBit_eq : fusionBit = fusionBitF (fun i => aCoefT[i]!) (fun i => fusionP[i]!)
    (fun i => fusionI[i]!) fRows := rfl

theorem lookA : (fun i => aCoefT[i]!) = fun i => pg 13 (mask 13) ACP i :=
  funext fun i => by rw [aCoefT_eq, getElem!_unpack_all kACP]

theorem lookP : (fun i => fusionP[i]!) = fun i => pg 13 (mask 13) FPP i :=
  funext fun i => by rw [fusionP_eq, getElem!_unpack_all kFPP]

theorem lookI : (fun i => fusionI[i]!) = fun i => pg 13 (mask 13) FIP i :=
  funext fun i => by rw [fusionI_eq, getElem!_unpack_all kFIP]

theorem xorR_add (p : Nat → Bool) (lo a : Nat) :
    ∀ b, xorR p lo (a + b) = Bool.xor (xorR p lo a) (xorR p (lo + a) b)
  | 0 => (Bool.xor_false _).symm
  | b + 1 => by
    have e1 : xorR p lo (a + (b + 1)) = Bool.xor (xorR p lo (a + b)) (p (lo + (a + b))) := rfl
    have e2 : xorR p (lo + a) (b + 1) = Bool.xor (xorR p (lo + a) b) (p (lo + a + b)) := rfl
    rw [e1, e2, xorR_add p lo a b, Bool.xor_assoc, Nat.add_assoc]

theorem xorR_congr {p q : Nat → Bool} {lo : Nat} :
    ∀ len, (∀ l < len, p (lo + l) = q (lo + l)) → xorR p lo len = xorR q lo len
  | 0, _ => rfl
  | len + 1, h => by
    have e : ∀ r : Nat → Bool, xorR r lo (len + 1) = Bool.xor (xorR r lo len) (r (lo + len)) :=
      fun _ => rfl
    rw [e, e, xorR_congr len fun l hl => h l (by omega), h len (by omega)]

theorem xorFold_eq (p : Nat → Bool) : ∀ n, xorFold n p = xorR p 0 n
  | 0 => by
    unfold xorFold
    rw [Nat.fold_zero]
    rfl
  | n + 1 => by
    have h := xorFold_eq p n
    unfold xorFold at h ⊢
    rw [Nat.fold_succ, h]
    change _ = Bool.xor (xorR p 0 n) (p (0 + n))
    rw [Nat.zero_add]

theorem xorR_blocks (p : Nat → Bool) :
    ∀ K, xorR p 0 (64 * K) = xorR (fun k => xorR p (64 * k) 64) 0 K
  | 0 => rfl
  | K + 1 => by
    have e : xorR (fun k => xorR p (64 * k) 64) 0 (K + 1) =
        Bool.xor (xorR (fun k => xorR p (64 * k) 64) 0 K) (xorR p (64 * (0 + K)) 64) := rfl
    rw [e, Nat.mul_succ, xorR_add, xorR_blocks p K, Nat.zero_add, Nat.zero_add]

end CertificateChecks.KernelJ2Cover

end

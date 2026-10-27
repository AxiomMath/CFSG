module

public import Certificates.Kernel.J2Cover.M22Dec
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Models
open CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.J2Cover.Models
open CFSG.Monster.B.Co2 (allLt_iff)

theorem allLt_eq_allN (n : Nat) (p : Nat → Bool) : allLt n p = allN n p :=
  Bool.eq_iff_iff.2 ⟨fun h => allN_of_forall (allLt_iff.1 h), fun h => allLt_iff.2 (allN_spec h)⟩

@[expose] noncomputable def cntR (p : Nat → Bool) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l ih => Nat.add ih (Bool.rec 0 1 (p l))) n

theorem countFold_eq (p : Nat → Bool) : ∀ n, countFold n p = cntR p n
  | 0 => by
    unfold countFold
    rw [Nat.fold_zero]
    rfl
  | n + 1 => by
    have h := countFold_eq p n
    unfold countFold at h ⊢
    rw [Nat.fold_succ, h]
    change _ = Nat.add (cntR p n) (Bool.rec 0 1 (p n))
    cases p n <;> rfl

theorem xor4725 (p : Nat → Bool) : xorFold 4725 p = xr4725 p := by
  unfold xr4725
  rw [xorFold_eq]
  have e : (4725 : Nat) = 64 * 73 + 53 := rfl
  rw [e, xorR_add, xorR_blocks, Nat.zero_add]

theorem lm_eq : (fun k b => (lmulTab[k]!)[b]!) = lmK := by
  funext k b
  unfold lmK lmulTab
  by_cases hk : k < 3
  · rw [blt_true hk, getElem!_ofFn' hk]
    by_cases hb : b < 128
    · rw [blt_true hb, getElem!_ofFn' hb]
    · rw [blt_false hb, getElem!_neg _ b (by rw [Array.size_ofFn]; exact hb)]
      rfl
  · rw [blt_false hk, getElem!_neg _ k (by rw [Array.size_ofFn]; exact hk)]
    rfl

theorem bt_eq : (fun a => betaTab[a]!) = btK := by
  funext a
  unfold btK betaTab
  by_cases ha : a < 128
  · rw [blt_true ha, getElem!_ofFn' ha]
  · rw [blt_false ha, getElem!_neg _ a (by rw [Array.size_ofFn]; exact ha)]
    rfl

theorem it_eq : (fun a => invTab[a]!) = itK := by
  funext a
  unfold itK invTab
  by_cases ha : a < 128
  · rw [blt_true ha, getElem!_ofFn' ha]
  · rw [blt_false ha, getElem!_neg _ a (by rw [Array.size_ofFn]; exact ha)]
    rfl

end CertificateChecks.KernelJ2Cover

end

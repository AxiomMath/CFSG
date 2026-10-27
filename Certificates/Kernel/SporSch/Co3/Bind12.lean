module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.Schreier.Co3Arrays
meta import CFSG.Sporadic.Schreier.Co3Arrays
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Co3Text12 CFSG.Sporadic.Schreier.Co3.co3Perm12Text

#ks_hexlines CertificateChecks.KernelSporSch.Co3Text12 CFSG.Sporadic.Schreier.Co3.co3Perm12Text 1 12 4

#ks_chars CertificateChecks.KernelSporSch.Co3Forms CFSG.Sporadic.Schreier.Co3.co3FormsText

#ks_hexlines CertificateChecks.KernelSporSch.Co3Forms CFSG.Sporadic.Schreier.Co3.co3FormsText 64 1 253

namespace CertificateChecks.KernelSporSch.Co3Text12

open CFSG.Sporadic.Schreier.Co3 CFSG.KS CFSG.KC.Enum

@[expose] noncomputable def hiOK (G : Nat) : Bool := Nat.beq (Nat.shiftRight G (12 * 4)) 0

theorem line_of {start cnt : Nat} {F : Nat → Nat} (hle : start + cnt ≤ 14)
    (h : allN cnt (fun j => Nat.beq (F j) (L (Nat.add start j))) = true) (j : Nat) (hj : j < cnt) :
    Native.hexLine co3Perm12Text.toUTF8 1 12 (start + j) = Raw.unpack 12 4 (F j) := by
  rw [eq, Nat.eq_of_beq_eq_true (allN_spec h j hj)]
  have hlt : start + j < 14 := by omega
  have := CFSG.KS.Text.hexBind_sound all (start + j) hlt
  rwa [Nat.zero_add] at this

theorem field_of {f start cnt : Nat} {F : Nat → Nat}
    (hl : co3Lines12.getD f (0, 0) = (start, cnt)) (hle : start + cnt ≤ 14)
    (h : allN cnt (fun j => Nat.beq (F j) (L (Nat.add start j))) = true) :
    (co3Field12 f).size = cnt ∧ ∀ j < cnt, (co3Field12 f)[j]! = Raw.unpack 12 4 (F j) := by
  have hsz : (co3Field12 f).size = cnt := by
    unfold co3Field12
    rw [Array.size_ofFn, hl]
  refine ⟨hsz, fun j hj => ?_⟩
  rw [getElem!_pos (co3Field12 f) j (hsz ▸ hj)]
  have e : (co3Field12 f)[j]'(hsz ▸ hj) = co3Arr12 ((co3Lines12.getD f (0, 0)).1 + j) := by
    unfold co3Field12
    exact Array.getElem_ofFn ..
  rw [e, hl]
  exact line_of hle h j hj

end CertificateChecks.KernelSporSch.Co3Text12

namespace CertificateChecks.KernelSporSch.Co3Forms

open CFSG.Sporadic.Schreier.Co3 CFSG.KS CFSG.KC.Enum

theorem word_eq {r : Nat} (hr : r < 276) : co3FormWord r = pg 253 (mask 253) (L r) 0 := by
  have h := CFSG.KS.Text.hexBind_sound all r hr
  rw [Nat.zero_add, ← eq] at h
  have h0 := congrArg (fun a : Array Nat => a[0]!) h
  simp only [Native.hexLine, Raw.unpack] at h0
  rw [getElem!_pos _ 0 (by simp), getElem!_pos _ 0 (by simp)] at h0
  simp only [Array.getElem_ofFn, Nat.mul_zero, Nat.add_zero] at h0
  rw [co3FormWord, Native.formAt, co3FormsBytes, Nat.mul_comm 65 r]
  exact h0

theorem word_lt {r : Nat} (hr : r < 276) : co3FormWord r < 2 ^ 253 := by
  rw [word_eq hr, pg, mask]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end CertificateChecks.KernelSporSch.Co3Forms

end

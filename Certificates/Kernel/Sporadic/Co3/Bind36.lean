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

#ks_chars CertificateChecks.KernelSpor.Co3Text36 CFSG.Sporadic.Schreier.Co3.co3Perm36Text

#ks_hexlines CertificateChecks.KernelSpor.Co3Text36 CFSG.Sporadic.Schreier.Co3.co3Perm36Text 2 36 6

namespace CertificateChecks.KernelSpor.Co3Text36

open CFSG.Sporadic.Schreier.Co3 CFSG.KS CFSG.KC.Enum

@[expose] noncomputable def hiOK (G : Nat) : Bool := Nat.beq (Nat.shiftRight G (36 * 6)) 0

theorem line_of {start cnt : Nat} {F : Nat → Nat} (hle : start + cnt ≤ 83)
    (h : allN cnt (fun j => Nat.beq (F j) (L (Nat.add start j))) = true) (j : Nat) (hj : j < cnt) :
    Native.hexLine co3Perm36Text.toUTF8 2 36 (start + j) = Raw.unpack 36 6 (F j) := by
  rw [eq, Nat.eq_of_beq_eq_true (allN_spec h j hj)]
  have hlt : start + j < 83 := by omega
  have := CFSG.KS.Text.hexBind_sound all (start + j) hlt
  rwa [Nat.zero_add] at this

theorem field_of {f start cnt : Nat} {F : Nat → Nat}
    (hl : co3Lines36.getD f (0, 0) = (start, cnt)) (hle : start + cnt ≤ 83)
    (h : allN cnt (fun j => Nat.beq (F j) (L (Nat.add start j))) = true) :
    (co3Field36 f).size = cnt ∧ ∀ j < cnt, (co3Field36 f)[j]! = Raw.unpack 36 6 (F j) := by
  have hsz : (co3Field36 f).size = cnt := by
    unfold co3Field36
    rw [Array.size_ofFn, hl]
  refine ⟨hsz, fun j hj => ?_⟩
  rw [getElem!_pos (co3Field36 f) j (hsz ▸ hj)]
  have e : (co3Field36 f)[j]'(hsz ▸ hj) = co3Arr36 ((co3Lines36.getD f (0, 0)).1 + j) := by
    unfold co3Field36
    exact Array.getElem_ofFn ..
  rw [e, hl]
  exact line_of hle h j hj

end CertificateChecks.KernelSpor.Co3Text36

end

module

public import Certificates.Kernel.Fi24PDc2.Glob
public import Certificates.Kernel.Fi24PDc2.Rec2
public import Certificates.Kernel.Fi24PDc2.Roots
public import Certificates.Kernel.LocalComp.Fi24TwoB.Shape25301

public section

namespace CFSG.KD.Fi24PDc2

open CFSG.KC.SLD2 CFSG.Sporadic.FischerOddCore

theorem dc_ok : dc2Check C D = true := by
  unfold dc2Check
  rw [glob, borbs, rec1s, frest, frows, rec2s, roots_ok, rootIdx]
  rfl

theorem lc_eq {l : Nat} (hl : l < 2) :
    LT.lc.getD (Nat.add 6 l) 0 = CertificateChecks.KernelSpor.Fi24PC.S l := by
  have h := codes
  rw [Bool.and_eq_true] at h
  interval_cases l
  · exact Nat.eq_of_beq_eq_true h.1
  · exact Nat.eq_of_beq_eq_true h.2

theorem ab_eq : ∀ l < 2, ∀ p < 378, (fi24PStrong[l]!)[p]! = L (Nat.add 6 l) p := by
  intro l hl p hp
  rw [CertificateChecks.KernelLC.Fi24Shape.pStrong (by omega),
    getElem!_pos _ p (by simpa [CFSG.KS.Raw.unpack] using hp)]
  simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
  unfold L
  rw [lc_eq hl]
  rfl

theorem sep_eq : D.sep = [0, 1, 2, 5] :=
  eq_of_beq sepB

theorem sb_size : SB.C.flatten.length = 256 :=
  eq_of_beq sbSize

open Certificates in
open CFSG.KD.Fi24PDc2 in
theorem facts :
    CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 378,
      (CFSG.Sporadic.FischerOddCore.fi24PStrong[l]!)[p]! = L (Nat.add 6 l) p) ∧
    shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 5] ∧ sbOK = true ∧
    SB.C.flatten.length = 256 :=
  ⟨dc_ok, ab_eq, shape, lets, sep_eq, sb, sb_size⟩

end CFSG.KD.Fi24PDc2

end

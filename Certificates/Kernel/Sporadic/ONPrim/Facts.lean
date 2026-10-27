module

public import Certificates.Kernel.Sporadic.ONPrim.All
public import Certificates.Kernel.Sporadic.ONNQ.Facts
public import CFSG.Certificates.Kernel.Spor.ONPrimSound

public section

namespace CertificateChecks.KernelSpor.ONPrim

open CFSG.KS.ONPrim CertificateChecks.KernelSpor.ONNQ

theorem pr_sound :
    (∀ y < 122760, labOf (ONPr.R y) < 5 ∧ repOf (labOf (ONPr.R y)) ≤ y) ∧
      (∀ g, g = 2 ∨ g = 3 → ∀ x < 122760, labOf (ONPr.R (TT g x)) = labOf (ONPr.R x)) ∧
      (∀ y < 122760, ∃ ks : List Nat, (∀ k ∈ ks, k < 2) ∧
        y = ks.foldr (fun k z => TT (2 + k) z) (repOf (labOf (ONPr.R y)))) ∧
      (∀ i < 5, ((Finset.range 122760).filter fun y => labOf (ONPr.R y) = i).card =
        primSizes.getD i 0) ∧
      (∀ i < 5, repOf i < 122760 ∧ labOf (ONPr.R (repOf i)) = i) :=
  prim_sound (UU := UU) (C := ONPr.C) (w := 1240) (k := 99)
    (fun x hx => ⟨(nq_perm x hx 2 (by decide)).1, (nq_perm x hx 2 (by decide)).2.2,
      (nq_perm x hx 3 (by decide)).1, (nq_perm x hx 3 (by decide)).2.2⟩)
    prBlAll prTot_ok (by decide) (by decide)

theorem pr_head : TT 2 0 = 0 ∧ TT 3 0 = 0 := primHead_sound prHead_ok

end CertificateChecks.KernelSpor.ONPrim

end

module

public import Certificates.Kernel.SporSch.HN.Pt2085K
public import Certificates.Data.Kernel.SporSch.HNXPathB
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2085

open CFSG.KC.LL.HNX CFSG.KD.HNPt2085 CFSG.KC.LL

@[expose] noncomputable def bndAt (c : Nat) : Bool := bndOk EN TW IS IDS (lgetL ST c)

theorem bnd : bndAt 0 = true ∧ bndAt 1 = true ∧ bndAt 2 = true ∧ bndAt 3 = true := by
  decide +kernel

theorem eb : ∀ l < 6, ∀ e < lget EN l, src l e < 1140000 ∧ dst l e < 1140000 := by
  decide +kernel

theorem pb : EN.length = 6 ∧ CH.length = 4 ∧ (∀ c < 4, lget CH c < 1140000) ∧
    (∀ t < 50, om t < 1140000) ∧ (∀ k < 6, ∀ t < 50, lget (lgetL IS k) t < 50) ∧
    (∀ k < 4, ∀ t < 50, lget (lgetL ES6 k) t < 50) := by
  decide +kernel

theorem neg_bnd : Bool.not (bndOk (EN.map (· - 1)) TW IS IDS (lgetL ST 3)) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNPt2085

end

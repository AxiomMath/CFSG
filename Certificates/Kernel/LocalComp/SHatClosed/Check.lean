module

public import Certificates.Kernel.LocalComp.SHatClosed.Rows
public import Certificates.Kernel.LocalComp.SHatClosed.Loops
public import CFSG.Certificates.Kernel.SHatClosedSound
public import CFSG.Certificates.Kernel.LocalCompPinSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.SHatD

open CFSG.KC.Enum CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.SHatClosed CFSG.KC.LocalComp.Pin
open CFSG.ComponentClassification.AS81.Census CFSG.ComponentClassification.AS81.SHatClosed

theorem gens_eq : (#[f2perm g1M, f2perm g2M] : Array (Array Nat)).size = SHatL.ng ∧
    ∀ k < SHatL.ng, (#[f2perm g1M, f2perm g2M] : Array (Array Nat))[k]! = unpack 64 7 (SHatL.G k) :=
  binds_of_listK rfl (by quickRfl)

theorem enum_eq : lEnum.tabs = Array.ofFn (n := SHatL.N) fun i => unpack 64 7 (SHatL.T i.val) :=
  (enumBFS_of_bfsK gens_eq.1 gens_eq.2 SHatL.ok (Nat.le_refl _)).2

theorem shat_checks : f1OK = true ∧ f2OK = true ∧ f3OK = true := by
  obtain ⟨h1, h2, h3⟩ := shatK_sound SHatL.ok invOK bindOK SHatR.all SHatCI.all fixOK SHatF.all
  rw [← enum_eq] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

end CertificateChecks.KernelLC.SHatD

end

module

public import Certificates.Kernel.Pk442010.Grp
public import Certificates.Data.OmegaPk

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KC.Pk442010

theorem tBmem : memP CQ.N CQ.T CQ.S tBL = true := by decide +kernel

theorem codes : (allN 24 fun i => Nat.blt (csAt csW i) 81 &&
    (Certificates.OmegaPk.wordTab.lookup (csAt csW i) ==
      some ((wsR.getD i []).map fun k => k != 0)) &&
    Nat.beq (csAt csW i) (Certificates.OmegaPk.code ((Certificates.OmegaPk.allSL ()).getD i 1))) =
      true := by
  decide +kernel

theorem sl_all : (∀ A : Certificates.OmegaPk.SL23, A ∈ Certificates.OmegaPk.allSL ()) ∧
    (Certificates.OmegaPk.allSL ()).length = 24 := by
  decide +kernel

theorem code28 : ∀ A : Certificates.OmegaPk.SL23, Certificates.OmegaPk.code A = 28 → A = 1 := by
  decide +kernel

end CertificateChecks.KernelPk442010

end

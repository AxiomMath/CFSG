module

public import Certificates.Kernel.Sporadic.OddCore.S8147Rnd
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KD.S8147 CFSG.KC.S2301 CertificateChecks.KernelSpor

@[expose] noncomputable def cellB (i : Nat) : Bool :=
  allN (nSteps i) fun s => strictB (Q (stageIdx i s)) fun q =>
    bAnd(tabOK (nat_lit 1782) (K (stageIdx i s)) (X (stageIdx i s)) q,
      Nat.ble (cellCntK (nat_lit 1782) q (rk q (point i s))) (bound i s))

end CertificateChecks.KernelSpor.S8147

#kc_slices CertificateChecks.KernelSpor.S8147.Cell CertificateChecks.KernelSpor.S8147.cellB 6

namespace CertificateChecks.KernelSpor.S8147

open CFSG.KC.Enum CFSG.KD.S8147 CFSG.KC.S2301 CertificateChecks.KernelSpor

theorem init0 : allN 1782 (initOK true (X 0) (Q 0) CFSG.KD.S2301.M (SFL12 0)) = true := by quickRfl
theorem init1 : allN 1782 (initOK true (X 26) (Q 26) CFSG.KD.S2301.M (SFL12 1)) = true := by
  quickRfl
theorem init2 : allN 1782 (initOK true (X 44) (Q 44) CFSG.KD.S2301.M (SFL12 2)) = true := by
  quickRfl
theorem init3 : allN 1782 (initOK true (X 62) (Q 62) CFSG.KD.S2301.M (SFL12 3)) = true := by
  quickRfl
theorem init4 : allN 1782 (initOK true (X 88) (Q 88) CFSG.KD.S2301.M (SFL12 4)) = true := by
  quickRfl
theorem init5 : allN 1782 (initOK true (X 114) (Q 114) CFSG.KD.S2301.M (SFL12 5)) = true := by
  quickRfl

theorem inj0 : injOK 1782 (X 25) (Q 25) (O 25) = true := by quickRfl
theorem inj1 : injOK 1782 (X 43) (Q 43) (O 43) = true := by quickRfl
theorem inj2 : injOK 1782 (X 61) (Q 61) (O 61) = true := by quickRfl
theorem inj3 : injOK 1782 (X 87) (Q 87) (O 87) = true := by quickRfl
theorem inj4 : injOK 1782 (X 113) (Q 113) (O 113) = true := by quickRfl
theorem inj5 : injOK 1782 (X 131) (Q 131) (O 131) = true := by quickRfl

theorem bindL : allN 6 (fun i => bindK 1782 (SFL12 i) (SFvT.F i)) = true := by quickRfl

theorem tltL : allN 6 (fun i => allN 1782 (fun v => Nat.blt (tg (SFL12 i) v) 1782)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.S8147

end

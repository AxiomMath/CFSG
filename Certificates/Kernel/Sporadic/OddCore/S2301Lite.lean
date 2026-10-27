module

public import Certificates.Kernel.Sporadic.OddCore.S2301Data
public import Certificates.Kernel.Sporadic.OddCore.S2301Gens
public import Certificates.Kernel.Sporadic.OddCore.S2301Idx
public import Certificates.Data.Kernel.Suz2301
import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.S2301

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301 CFSG.KC.S2301

@[expose] noncomputable def cellB (i : Nat) : Bool :=
  allN (nSteps i) fun s => strictB (Q (stageIdx i s)) fun q =>
    bAnd(tabOK (nat_lit 1782) (K (stageIdx i s)) (X (stageIdx i s)) q,
      Nat.ble (cellCntK (nat_lit 1782) q (rk q (point i s))) (bound i s))

end CertificateChecks.KernelSpor.S2301

#kc_slices CertificateChecks.KernelSpor.S2301.Cell CertificateChecks.KernelSpor.S2301.cellB 4

namespace CertificateChecks.KernelSpor.S2301

open CFSG.KC.Enum CFSG.KC.N3153 CFSG.KD.S2301 CFSG.KC.S2301

theorem init0 : allN 1782 (initOK true (X 0) (Q 0) M (GP 3)) = true := by quickRfl
theorem init1 : allN 1782 (initOK true (X 38) (Q 38) M (GP 4)) = true := by quickRfl
theorem init2 : allN 1782 (initOK false (X 72) (Q 72) M (GP 5)) = true := by quickRfl
theorem init3 : allN 1782 (initOK true (X 101) (Q 101) M (GP 6)) = true := by quickRfl

theorem inj0 : injOK 1782 (X 37) (Q 37) (O 37) = true := by quickRfl
theorem inj1 : injOK 1782 (X 71) (Q 71) (O 71) = true := by quickRfl
theorem inj2 : injOK 1782 (X 100) (Q 100) (O 100) = true := by quickRfl
theorem inj3 : injOK 1782 (X 136) (Q 136) (O 136) = true := by quickRfl

end CertificateChecks.KernelSpor.S2301

end

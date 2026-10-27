module

public import Certificates.Kernel.Sporadic.OddCore.McLO
meta import CFSG.Sporadic.SmallOddCore.McLLocalCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore

meta def coverM : Array (Array Nat) :=
  let idxs := mclXOrbits.map fun e => indexOf e.tabs
  mclXEnum.tabs.map fun t =>
    let l := ((List.range 14).find? fun l => (idxs[l]!).contains t).getD 0
    #[65536 * l + (idxs[l]!).getD t 0]

end CertificateChecks.KernelSpor.McL2287

#kmisc_packarrs CertificateChecks.KernelSpor.MCOV CertificateChecks.KernelSpor.McL2287.coverM 32

namespace CertificateChecks.KernelSpor.McL2287

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexAt

@[expose] noncomputable def coverK (k : Nat) : Bool :=
  strictB (MCOV k) (fun wk =>
    strictB (Nat.shiftRight wk 16) (fun l => strictB (Nat.land wk 65535) (fun q =>
      bAnd(Nat.blt l 14, bAnd(Nat.blt q (MOF.C l),
        Nat.beq (offF MOF.T (MOF.TO l) q) (MXE.T k))))))

theorem cover0 : allBlk 0 coverK 5040 = true := by quickRfl
theorem cover1 : allBlk 5040 coverK 5040 = true := by quickRfl
theorem cover2 : allBlk 10080 coverK 5040 = true := by quickRfl
theorem cover3 : allBlk 15120 coverK 5040 = true := by quickRfl

end CertificateChecks.KernelSpor.McL2287

end


module

public import Certificates.Kernel.UnitarySix.YamadaBase
public import CFSG.Certificates.Kernel.U6SoundTables
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks

public section

#u6_tables CertificateChecks.KernelU6.T

namespace CertificateChecks.KernelU6

open CFSG.KC.U6

theorem kPosn : posnOK U.POS T.POSN = true := by quickRfl
theorem kMV : mvOK U.UP T.MVT = true := by quickRfl

@[expose] noncomputable def kRF (s : Nat) : Bool := rowsOK U.UP T.POSN T.MVT T.R (33 * s) 33

@[expose] noncomputable def kSF (s : Nat) : Bool := swapK T.R (33 * s) 33

#kc_each_unfold kRF 0 21 as CertificateChecks.KernelU6.kR
#kc_each_unfold kSF 0 21 as CertificateChecks.KernelU6.kS

theorem kTables : TabsOK U.UP U.POS T.POSN T.MVT T.R := by
  refine ⟨kPosn, kMV, fun s hs => ?_⟩
  interval_cases s
  exacts [kR0, kR1, kR2, kR3, kR4, kR5, kR6, kR7, kR8, kR9, kR10, kR11, kR12, kR13, kR14, kR15,
    kR16, kR17, kR18, kR19, kR20]

#kc_forall_chunks kSwapK (fun s => swapK T.R (33 * s) 33 = true) 21 CertificateChecks.KernelU6.kS 1

theorem kSwap : ∀ s < 21, swapK T.R (33 * s) 33 = true := kSwapK

end CertificateChecks.KernelU6

end

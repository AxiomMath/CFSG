module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4ModT10Data
import CFSG.Certificates.Kernel.T10CodeASound
import Certificates.Kernel.T10.Checks
import Certificates.Kernel.T10.ChecksA

public section

namespace Certificates.Kernel.T10

open CFSG.OddStandard.AltStdSmall4.ModT10 CFSG.KC.T10Code

theorem t10CheckB_kernel : t10CheckB () = true :=
  t10CheckB_of (fun _ hj => atW_PL hj) (all_of_chunks ch36401B0 ch36401B1 ch36401B2 ch36401B3
    ch36401B4 ch36401B5 ch36401B6 ch36401B7)

theorem t10CheckC_kernel : t10CheckC () = true := by
  have hT := ch36401T
  simp only [Bool.and_eq_true, beq_iff_eq] at hT
  exact t10CheckC_of (fun _ hj => atW_PL hj) hT.1 hT.2 (all_of_chunks ch36401C0 ch36401C1
    ch36401C2 ch36401C3 ch36401C4 ch36401C5 ch36401C6 ch36401C7)

theorem t10CheckA_kernel : t10CheckA () = true :=
  t10CheckA_of (fun _ hj => atW_PL hj)
    (orbD_ok ch36401AO0 ch36401AO1 ch36401AO2 ch36401AO3 ch36401AO4)
    (all_of_chunks ch36401AL0 ch36401AL1 ch36401AL2 ch36401AL3 ch36401AL4 ch36401AL5
      ch36401AL6 ch36401AL7)
    (allR0 ch36401AK) (allR0 ch36401AC) (allR0 ch36401AR) ch36401AD

end Certificates.Kernel.T10

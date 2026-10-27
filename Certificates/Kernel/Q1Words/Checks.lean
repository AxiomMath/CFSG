module

public import Certificates.Data.Kernel.OmegaPacked
public import CFSG.RankThree.PartOne.SEITZQ1.WordInputs

public section

namespace Certificates.Kernel.Q1Words

open CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.SEITZQ1 Certificates.OmegaPacked

set_option maxHeartbeats 0 in
theorem check_nz2_even : omegaCheckP Tag.F4 (q1Full false false) (q1Target false) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem check_nz2_odd : omegaCheckP Tag.F4 (q1Full true false) (q1Target false) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem check_b10_even : omegaCheckP Tag.F4 (q1Full false true) (q1Target true) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem check_b10_odd : omegaCheckP Tag.F4 (q1Full true true) (q1Target true) = true := by
  decide +kernel

end Certificates.Kernel.Q1Words

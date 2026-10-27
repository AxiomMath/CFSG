module

public import Certificates.Data.Kernel.EvenSporDS81.FCDefs
import CFSG.Certificates.Kernel.Common.StrLitToList
import CFSG.Certificates.Kernel.EvenSporDS81.FCFast

public section

namespace CertificateChecks.KernelEvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81 CFSG.KC.EvenSporDS81

set_option maxRecDepth 100000

theorem fc_cols : uqMs.toList.all fcColsLt = true := by
  decide +kernel

private theorem uq_treeOK : treeOK (uqMs.toList.map keyA) (idxTree (uqMs.toList.map keyA)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem fc_tab : tabAllL (tabK (uqMs.toList.map keyA)) uqMs.size = true := by
  rw [tabK_eq uq_treeOK]
  decide +kernel

set_option maxHeartbeats 0 in
theorem fc_rest : fcRestL (uqCols uqW uqSg0).toList (uqCols uqW uqSg1).toList uqMs.toList uqFam
    (tabK (uqMs.toList.map keyA)) = true := by
  simp only [uqCols, uqSg0, uqSg1, uqSg0S, uqSg1S, uqDecode, List.map_toArray, List.map_cons,
    List.map_nil, CFSG.KC.StrLitToList.strLitToList]
  decide +kernel

set_option maxHeartbeats 0 in
theorem fc_dist : fcDistinct uqMs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem fc_fix : fixOKL uqMs.toList (idxL uqMs.toList idColsK) uqFam = true := by
  decide +kernel

end CertificateChecks.KernelEvenSporDS81

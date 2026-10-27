module

public import Certificates.Data.S5RowsU33
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups Certificates.S5Rows Certificates.S5RowsU33 CFSG.Certificates.Kernel.PkEnum

theorem qs_516001K : schP QSA = true ∧ orderV QSA = 64 := by
  constructor <;> decide +kernel

theorem le_516001K : (QSA.original.toList.all fun g => siftP U33.QA g 0) = true := by
  decide +kernel

theorem f1a_516001K :
    threeCycCheck (elemsV QSA) (elemsV U33.QP) (fun x => siftP U33.QP x 0) = true := by
  decide +kernel

theorem f1b_516001K :
    conjMulCheck (elemsV QSA) (elemsV U33.QA) (fun x => siftP U33.QP x 0) = true := by
  decide +kernel

theorem f1c_516001K : uniqueOuterCheck (elemsV QSA) (fun x => siftP U33.QP x 0) = true := by
  decide +kernel

end CertificateChecks.KernelKGroupsE

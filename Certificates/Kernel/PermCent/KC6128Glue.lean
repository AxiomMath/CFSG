module

public import Certificates.Kernel.PermCent.KC6128
public import Certificates.Kernel.PermCent.KG5137
public import CFSG.Certificates.Kernel.PermCent.L216CensusSound

public section

namespace CFSG.Certificates.Kernel.PkCV.L216C.K6128

open CFSG.GH74.Uniqueness.SU.K.R4.L216M CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.PkCV.KGrp

theorem kCensus : Certificates.Seitz77Sec27.l216CensusCheck = true := by
  have hb : ∀ j < 8, clsBlk 2040 j = true := by
    intro j hj
    match j, hj with
    | 0, _ => exact kB0
    | 1, _ => exact kB1
    | 2, _ => exact kB2
    | 3, _ => exact kB3
    | 4, _ => exact kB4
    | 5, _ => exact kB5
    | 6, _ => exact kB6
    | 7, _ => exact kB7
  rw [census_eq]
  exact census_of (check_certificate_of _ _ _ _ _ K5137.kQP.1) (clsOK_of_blocks 8 hb kTl) kC1 kC2
    (mem_of_memN kM.1) (not_mem_of_memN kM.2)

end CFSG.Certificates.Kernel.PkCV.L216C.K6128

end

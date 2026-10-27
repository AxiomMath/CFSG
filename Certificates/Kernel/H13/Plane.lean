module

public import CFSG.Quasithin.H13.L32NS8PlaneInputs
import CFSG.Certificates.Kernel.Mat8KSound

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.S8Cert CFSG.KC.Mat8K

theorem t8BasicB_true : t8BasicB = true := by
  simp only [t8BasicB, t8E, t8G, subB, closedB, nodupB_eq, elemsOf_eq, hs_contains_ofList',
    hs_contains_ofList, contains_eq_memL, mul8_toK, mv8_toK, evalW_toK]
  decide +kernel

theorem t8FixB_true : t8FixB = true := by
  simp only [t8FixB, t8G, mv8_toK, evalW_toK]
  decide +kernel

theorem t8PlaneB_true : t8PlaneB = true := by
  simp only [t8PlaneB, t8G, mv8_toK, evalW_toK]
  decide +kernel

theorem s8IIB_true : s8IIB = true := by
  simp only [s8IIB, mv8_toK]
  decide +kernel

theorem tvB_true : tvB = true := by
  simp only [tvB, evalW_toK]
  decide +kernel

theorem planeCheck_true : planeCheck = true := by
  rw [planeCheck, t8BasicB_true, t8FixB_true, t8PlaneB_true, s8IIB_true, tvB_true]
  rfl

end CertificateChecks.KernelH13

end

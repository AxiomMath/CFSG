module

public import CFSG.Quasithin.H13.L32NO3Inputs
public import CFSG.Certificates.Kernel.Mat8PSound
public import Certificates.Kernel.H13.Data

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert CFSG.KC.Mat8P

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem om3L_eq : elemsP (o3G.map code64R) = D.om3L := by decide +kernel

set_option maxHeartbeats 0 in
theorem om3FL_eq : elemsP ((o3G ++ [fG]).map code64R) = D.om3FL := by decide +kernel

set_option maxHeartbeats 0 in
theorem omNL_eq : elemsP ((o3G ++ [fG, sG]).map code64R) = D.omNL := by decide +kernel

set_option maxHeartbeats 0 in
theorem h1L_eq : elemsP ((o3G ++ [sG]).map code64R) = D.h1L := by decide +kernel

set_option maxHeartbeats 0 in
theorem h2L_eq : elemsP ((o3G ++ [sfG]).map code64R) = D.h2L := by decide +kernel

theorem om3E_eq : om3E = D.om3L.map unpackM := by
  rw [om3E, elemsOf_eqP _ (by decide), om3L_eq]

theorem om3FE_eq : om3FE = D.om3FL.map unpackM := by
  rw [om3FE, elemsOf_eqP _ (by decide), om3FL_eq]

theorem omNE_eq : omNE = D.omNL.map unpackM := by
  rw [omNE, elemsOf_eqP _ (by decide), omNL_eq]

theorem h1E_eq : h1E = D.h1L.map unpackM := by
  rw [h1E, elemsOf_eqP _ (by decide), h1L_eq]

theorem h2E_eq : h2E = D.h2L.map unpackM := by
  rw [h2E, elemsOf_eqP _ (by decide), h2L_eq]

end CertificateChecks.KernelH13

end

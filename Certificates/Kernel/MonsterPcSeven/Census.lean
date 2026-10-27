module

public import CFSG.Certificates.Kernel.MonsterPcSeven.Cover
public import Certificates.Kernel.MonsterPcSeven.Check0
public import Certificates.Kernel.MonsterPcSeven.Check1
public import Certificates.Kernel.MonsterPcSeven.Check2
public import Certificates.Kernel.MonsterPcSeven.Check3
public import Certificates.Kernel.MonsterPcSeven.Check4
public import Certificates.Kernel.MonsterPcSeven.Check5
public import Certificates.Kernel.MonsterPcSeven.Check6
public import Certificates.Kernel.MonsterPcSeven.Fus

public section

namespace CertificateChecks.KernelM7.PcSeven

open CFSG.KC.MonPcSeven CFSG.KC.MonPcSevenD

theorem censusFact : CensusFact := by
  have hC : ∀ k < 49, chunkOK rep 432 (2401 * k) (chunks.getD k []) = true := by
    intro k hk
    have pick : ∀ j : ℕ, j ≤ k → k < j + 7 →
        (∀ l < 7, chunkOK rep 432 (2401 * (j + l)) (chunks.getD (j + l) []) = true) →
        chunkOK rep 432 (2401 * k) (chunks.getD k []) = true := fun j h1 h2 hc => by
      have e : j + (k - j) = k := by omega
      have := hc (k - j) (by omega)
      rwa [e] at this
    by_cases h0 : k < 7
    · exact pick 0 (by omega) (by omega) m7census0
    by_cases h1 : k < 14
    · exact pick 7 (by omega) (by omega) m7census1
    by_cases h2 : k < 21
    · exact pick 14 (by omega) (by omega) m7census2
    by_cases h3 : k < 28
    · exact pick 21 (by omega) (by omega) m7census3
    by_cases h4 : k < 35
    · exact pick 28 (by omega) (by omega) m7census4
    by_cases h5 : k < 42
    · exact pick 35 (by omega) (by omega) m7census5
    · exact pick 42 (by omega) (by omega) m7census6
  exact census_fact (elem_of_chunks hC m7len) m7fus

theorem phiOK_true : ∀ k < 7, phiOK (343 * k) 343 = true := m7phi

end CertificateChecks.KernelM7.PcSeven

end

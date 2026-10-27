module

public import Certificates.Kernel.Fi22Core.Final
public import Certificates.Kernel.Fi22Core.OrbBfs
import CFSG.F3.ConjBFS

public section

namespace CertificateChecks.KernelFi22C

open CFSG.Sporadic.Fi22.Native CFSG.F3.Native CFSG.Sporadic.Th.Native CFSG.KS.Fi22L

theorem orbitData_eq : orbitData () = orbL := by
  have h := fi22_cert
  simp only [Bool.and_eq_true] at h
  have hc := h.1.1.2
  have hs : orbL.keys.size = 3510 := keys_size
  unfold orbitData
  refine BfsSpec.conjBFS_eq_of (fa := orbEntry 0) (fb := orbEntry 1) (fp := orbEntry 2)
    (fl := orbEntry 3) hc (by omega) (by rw [hs]; exact orbTab_size 0)
    (by rw [hs]; exact orbTab_size 1) (by rw [hs]; exact orbTab_size 2)
    (by rw [hs]; exact orbTab_size 3) (fun i hi => ap_orbTab (by omega))
    (fun i hi => ap_orbTab (by omega)) (fun i hi => ap_orbTab (by omega))
    (fun i hi => ap_orbTab (by omega)) ?_
  rw [hs]
  exact orbL_bfs

end CertificateChecks.KernelFi22C

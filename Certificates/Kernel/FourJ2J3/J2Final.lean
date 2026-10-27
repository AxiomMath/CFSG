module

public import Certificates.Kernel.FourJ2J3.Glue
public import Certificates.Kernel.FourJ2J3.J2Checks
public import CFSG.Certificates.Kernel.FourJoinedKSound

public section

namespace CertificateChecks.KernelFourJ2J3

open CFSG.ComponentClassification.Sol76.Sig.GSYard02 CFSG.Sporadic.Schreier CFSG.KC.FourJ
open CertificateChecks.KernelSporSch CertificateChecks.KernelFourJ

theorem subP_j2 : subP 315 9 (PJ2.S 0) (PJ2.S 1) = j2P := by
  rw [subP, j2P, j2Gen, j2Gen, j2StrongPerm, j2StrongPerm, ← PJ2.arr_eq 0 (by norm_num),
    ← PJ2.arr_eq 1 (by norm_num)]

theorem n128_j2 : J2D.N = 128 := by
  have h := J2.nums
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem sylowFourJoined_j2P_kernel :
    SylowFourJoined ↥j2P := by
  obtain ⟨hKP, hK, ⟨d⟩⟩ := fjK_sound J2.gens J2.bfs (by decide) J2.keys J2.klein J2.tree J2.iso
    J2.norm J2.gen J2.comp
  rw [subP_j2] at hKP d
  exact sylowFourJoined_j2P_of_data hKP (by rw [hK, n128_j2]) d

end CertificateChecks.KernelFourJ2J3

end

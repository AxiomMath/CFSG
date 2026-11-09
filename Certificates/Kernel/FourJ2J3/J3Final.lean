module

public import Certificates.Kernel.FourJ2J3.Glue
public import Certificates.Kernel.FourJ2J3.J3Checks
public import Certificates.Kernel.SporSch.PairJ3.Check2236
public import CFSG.Certificates.Kernel.FourJoinedKSound
public import Certificates.Kernel.FourJ2J3.J3BSound

public section

namespace CertificateChecks.KernelFourJ2J3

open CFSG.ComponentClassification.Sol76.Sig.GSYard02 CFSG.Sporadic.Schreier CFSG.KC.FourJ
open CertificateChecks.KernelSporSch CertificateChecks.KernelFourJ

theorem subP_j3 : subP 6156 13 (PJ3.S 0) (PJ3.S 1) = j3P := by
  rw [subP, j3P, j3Gen, j3Gen, j3StrongPerm, j3StrongPerm, ← PJ3Cert.arr_eq 0 (by norm_num),
    ← PJ3Cert.arr_eq 1 (by norm_num)]

theorem n128_j3 : J3D.N = 128 := by
  have h := J3.nums
  simp only [Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1

theorem sylowFourJoined_j3P_kernel :
    SylowFourJoined ↥j3P := by
  obtain ⟨K, hKP, hK, ⟨d⟩⟩ := J3B.j3_fourJoined
  rw [subP_j3] at hKP d
  exact sylowFourJoined_j3P_of_data hKP hK d

end CertificateChecks.KernelFourJ2J3

end

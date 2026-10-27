module

public import Certificates.Kernel.Q3Wit.Checks
public import Certificates.Kernel.SchreierFam.J3CqBind
public import Certificates.Kernel.Census.J2H.Checks
public import CFSG.Certificates.Kernel.WitKSound
public import CFSG.ClassicalInvolution.Q3.Q3SJ2Inputs
public import CFSG.ClassicalInvolution.Q3.Q3SJ3Inputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ3Wit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.WitK CFSG.KC.BfsPin
open CertificateChecks.KernelJ2Cover CertificateChecks.KernelJ2H
  CertificateChecks.KernelSchreierFam.J3Cq
open CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.J3Data

theorem j2_check : CFSG.ClassicalInvolution.Q3.j2WitnessCheck = true := by
  have hw : szOK 315 9 = true := by decide +kernel
  have hp := j2Perm
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨p0, p1⟩, pz⟩ := hp
  have P0 := pp_of_permB hw p0
  have P1 := pp_of_permB hw p1
  have PZ := pp_of_permB hw pz
  have e0 : cent2AStrong[0]! = unpack 315 9 (C2A.S 0) := c2A_binds.2.2.2.2.1 0 (by norm_num)
  have e1 : cent2AStrong[1]! = unpack 315 9 (C2A.S 1) := c2A_binds.2.2.2.2.1 1 (by norm_num)
  have ez : twoAArr = unpack 315 9 (S0C.S 0) := arrBind_sound s0_z
  unfold CFSG.ClassicalInvolution.Q3.j2WitnessCheck CFSG.ClassicalInvolution.Q3.j2WitnessG₁
    CFSG.ClassicalInvolution.Q3.j2WitnessG₂
  rw [e0, e1, ez, compA_PP P0 P1, compA_PP P1 P0, compA_PP (P0.mul P1) (P0.mul P1),
    compA_PP (P1.mul P0) (P1.mul P0),
    witnessCheckA_PP hw ((P0.mul P1).mul (P0.mul P1)) ((P1.mul P0).mul (P1.mul P0)) PZ]
  exact j2Wit

theorem j3_check : CFSG.ClassicalInvolution.Q3.j3WitnessCheck = true := by
  have hw := CertificateChecks.KernelSchreierFam.J3CqBind.hsz
  have P0 := pp_of_permB hw (CertificateChecks.KernelSchreierFam.J3CqBind.kk_perm 0 (by norm_num))
  have P1 := pp_of_permB hw (CertificateChecks.KernelSchreierFam.J3CqBind.kk_perm 1 (by norm_num))
  have PA := pp_of_permB hw (CertificateChecks.KernelSchreierFam.J3CqBind.ab_perm 0 (by norm_num))
  have e0 := CertificateChecks.KernelSchreierFam.J3CqBind.kk_bind 0 (by norm_num)
  have e1 := CertificateChecks.KernelSchreierFam.J3CqBind.kk_bind 1 (by norm_num)
  have ea := CertificateChecks.KernelSchreierFam.J3CqBind.ab_bind 0 (by norm_num)
  have q1 := P1.mul P0
  have q2 := P0.mul q1
  have q3 := P1.mul q2
  have q4 := P1.mul q3
  have q5 := P0.mul q4
  have q6 := P0.mul q5
  have q7 := P1.mul q6
  unfold CFSG.ClassicalInvolution.Q3.j3WitnessCheck CFSG.ClassicalInvolution.Q3.j3WitnessG₁
    CFSG.ClassicalInvolution.Q3.j3WitnessG₂
  rw [e0, e1, ea, compA_PP P0 P1, compA_PP P1 P0, compA_PP P0 q1, compA_PP P1 q2,
    compA_PP P1 q3, compA_PP P0 q4, compA_PP P0 q5, compA_PP P1 q6,
    witnessCheckA_PP hw (P0.mul P1) q7 PA]
  exact j3Wit

end CertificateChecks.KernelQ3Wit

end

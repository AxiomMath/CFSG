module

public import Certificates.Kernel.MatCert.HeringFp
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsFpKSound
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.Ord CFSG.KS.SporSch.LyM
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem fourHeMcert : mcertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    CFSG.RankThree.PartTwo.Sec21.Hering214.FourHe.cert = true := by
  have h := fourHe_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine mcertCheck_of_N (homP heConsts (by norm_num)) ?_ ?_ hA hB h
  · rw [HeS1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · rw [HeS2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

theorem fourJ2Mcert : mcertCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2
    CFSG.RankThree.PartTwo.Sec21.Hering214.FourJ2.cert = true := by
  have h := fourJ2_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine mcertCheck_of_N (homP j2Consts (by norm_num)) ?_ ?_ hA hB h
  · rw [J2S1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · rw [J2S2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

end CertificateChecks.KernelMC

end

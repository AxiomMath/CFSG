module

public import Certificates.Kernel.MatCert.HeringON
public import Certificates.Kernel.MatCert.K135ON
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsFpKSound
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KC.OpsLayK
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

theorem ks12ONMcert : mcertCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    CFSG.RankThree.PartTwo.KFacts.KS12ON.cert = true :=
  mcertL_sound (d := 154) KernelTc.ON.lay_ok rfl rfl KernelTc.ON.decA KernelTc.ON.decB
    KernelTc.ON.LA_eq KernelTc.ON.LB_eq ks12ON_K

theorem k135ONMcert : mcertCheck (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    CFSG.RankThree.PartTwo.Sec13.F135Last.K135.onCert = true := by
  have h := k135ON_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine mcertCheck_of_N (homP onConsts (by norm_num)) ?_ ?_ hA hB h
  · rw [ONS1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · rw [ONS2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

end CertificateChecks.KernelMC

end

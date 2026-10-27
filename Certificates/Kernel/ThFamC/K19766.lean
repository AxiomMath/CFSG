module

public import Certificates.Data.McLFiveTables
public import Certificates.Kernel.Census.McLChain
public import Certificates.Kernel.LocalComp.McLCent

public section

namespace CertificateChecks.KernelThFamC.K19766

open CFSG.KC.Misc.HexFlat CFSG.KS.Raw

theorem strong_eq (j : Nat) (hj : j < 13) :
    CFSG.Sporadic.Schreier.mclStrongArrs[j]! =
      unpack 275 9 (CertificateChecks.KernelCensus.McLS.F j) := by
  have h := hexTable_sound CertificateChecks.KernelCensus.McLS.all j hj
  rw [← CertificateChecks.KernelCensus.McLS.eq] at h
  rw [← h, CFSG.Sporadic.Schreier.mclStrongArrs, getElem!_pos _ _ (by simp; omega),
    Array.getElem_ofFn]

theorem tabA : unpack 275 9 (CertificateChecks.KernelCensus.McLS.F 0) =
    Certificates.MaxD2Heis.mclTabA := by decide +kernel

theorem tabB : unpack 275 9 (CertificateChecks.KernelCensus.McLS.F 1) =
    Certificates.MaxD2Heis.mclTabB := by decide +kernel

theorem tabU : unpack 275 9 (CertificateChecks.KernelLC.McLC.MC.F 0) =
    Certificates.MaxD2Heis.mclTabU := by decide +kernel

open Certificates in
theorem facts : CFSG.Sporadic.Schreier.mclStrongArrs[0]! = Certificates.MaxD2Heis.mclTabA ∧
    CFSG.Sporadic.Schreier.mclStrongArrs[1]! = Certificates.MaxD2Heis.mclTabB ∧
    CFSG.Sporadic.SmallOddCore.Native.natArr CFSG.Sporadic.SmallOddCore.mclOuterTbl =
      Certificates.MaxD2Heis.mclTabU ∧
    Certificates.MaxD2Heis.mclTabA.size = 275 ∧ Certificates.MaxD2Heis.mclTabB.size = 275 ∧
    Certificates.MaxD2Heis.mclTabU.size = 275 := by
  refine ⟨?_, ?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · rw [strong_eq 0 (by norm_num), tabA]
  · rw [strong_eq 1 (by norm_num), tabB]
  · rw [CFSG.Sporadic.SmallOddCore.mclOuterTbl,
      CertificateChecks.KernelLC.McLC.natArr_cent 0 (by norm_num), tabU]

end CertificateChecks.KernelThFamC.K19766

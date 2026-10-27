module

public import Certificates.Kernel.LocalComp.McLCent
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuterCheckInputs
public import CFSG.Certificates.Kernel.LocalCompPermSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.McLY

open CertificateChecks.KernelLC.McLC CFSG.KS.Raw CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.RestrictedStd.Spor CFSG.PSL3Four.Native CFSG.KC.LocalComp.Perm

@[expose] def yG : Array Tab :=
  #[#[0, 10, 6, 2, 7, 5, 3, 9, 1, 4, 8], #[2, 10, 0, 3, 4, 6, 5, 7, 9, 8, 1],
    #[10, 8, 0, 7, 5, 1, 2, 6, 3, 4, 9], #[7, 0, 6, 2, 5, 10, 3, 1, 8, 9, 4]]

@[expose] def yGI : Array Tab :=
  #[#[0, 8, 3, 6, 9, 5, 2, 4, 10, 7, 1], #[2, 10, 0, 3, 4, 6, 5, 7, 9, 8, 1],
    #[2, 5, 6, 8, 9, 4, 7, 3, 1, 10, 0], #[1, 7, 3, 6, 10, 4, 2, 0, 8, 9, 5]]

theorem mclFix1_eq : mclFix1 = [37, 71, 102, 128, 140, 182, 207, 222, 226, 257, 272] := by
  rw [mclFix1, mclU1Arr, natArr_cent 17 (by norm_num)]
  decide +kernel

theorem mclYGens_eq : mclYGens = yG := by
  have h : (fun k : Fin 4 => restrictArr mclFix1
      (CFSG.Sporadic.SmallOddCore.Native.natArr (mclCentTbl (k.val + 18)))) =
      fun k : Fin 4 => restrictArr [37, 71, 102, 128, 140, 182, 207, 222, 226, 257, 272]
        (unpack 275 9 (MC.F (k.val + 18))) := by
    funext k
    rw [natArr_cent _ (by omega), mclFix1_eq]
  rw [mclYGens, h]
  decide +kernel

theorem mclYInvs_eq : mclYInvs = yGI := by
  rw [mclYInvs, mclYGens_eq]
  exact map_invTab_of_K (by decide +kernel)

theorem permOK_cent (k : ℕ) (hk : k < 22) (h : permK 275 (unpack 275 9 (MC.F k)) = true) :
    permOK 275 (mclCentTbl k) = true := by
  rw [permOK, natArr_cent k hk]
  exact isInvA_invCand_of_K h

theorem basic : mclFix1.length = 11 ∧ mclYGens.size = 4 ∧ invsOK 11 mclYGens mclYInvs = true ∧
    mclYOrbits.size = 10 ∧ permOK 275 (mclCentTbl 17) = true ∧
    ∀ k < 4, permOK 275 (mclCentTbl (k + 18)) = true := by
  refine ⟨by rw [mclFix1_eq]; rfl, by rw [mclYGens_eq]; rfl, ?_,
    by rw [mclYOrbits, Array.size_ofFn],
    permOK_cent 17 (by norm_num) (by decide +kernel), ?_⟩
  · rw [mclYInvs_eq, mclYGens_eq]
    decide +kernel
  · intro k hk
    interval_cases k
    · exact permOK_cent 18 (by norm_num) (by decide +kernel)
    · exact permOK_cent 19 (by norm_num) (by decide +kernel)
    · exact permOK_cent 20 (by norm_num) (by decide +kernel)
    · exact permOK_cent 21 (by norm_num) (by decide +kernel)

end CertificateChecks.KernelLC.McLY

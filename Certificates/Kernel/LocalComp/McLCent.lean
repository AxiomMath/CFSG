module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLCheckInputs
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
meta import CFSG.Sporadic.SmallOddCore.McLData
public import CFSG.Certificates.Kernel.Spor.RawSound

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.McLC.MC CFSG.Sporadic.SmallOddCore.mclCentHex
#kmisc_hexflat CertificateChecks.KernelLC.McLC.MC CFSG.Sporadic.SmallOddCore.mclCentHex 3 275 9 22

namespace CertificateChecks.KernelLC.McLC

open CFSG.KC.Misc.HexFlat CFSG.KS.Raw CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore

theorem natArr_cent (k : ℕ) (hk : k < 22) :
    CFSG.Sporadic.SmallOddCore.Native.natArr (mclCentTbl k) = unpack 275 9 (MC.F k) := by
  rw [mclCentTbl, MC.eq]
  exact hexT_sound MC.all (by norm_num) k hk

theorem mclXGens_eq : mclXGens =
    #[#[0, 4, 22, 18, 1, 5, 26, 14, 23, 29, 17, 12, 11, 13, 7, 15, 16, 10, 3, 19, 20, 32, 2, 8, 24,
        25, 6, 34, 28, 9, 30, 33, 21, 31, 27],
      #[20, 16, 9, 24, 13, 17, 33, 1, 26, 5, 4, 6, 18, 12, 23, 21, 28, 8, 0, 15, 10, 31, 14, 3, 32,
        19, 34, 22, 11, 30, 25, 29, 27, 7, 2]] := by
  have h : (fun k : Fin 2 => restrictArr mclFix
      (CFSG.Sporadic.SmallOddCore.Native.natArr (mclCentTbl (k.val + 5)))) =
      fun k : Fin 2 => restrictArr (fixedList 275 (unpack 275 9 (MC.F 4)))
        (unpack 275 9 (MC.F (k.val + 5))) := by
    funext k
    rw [natArr_cent _ (by omega), mclFix, mclT0Arr, natArr_cent 4 (by norm_num)]
  rw [mclXGens, h]
  decide +kernel

end CertificateChecks.KernelLC.McLC

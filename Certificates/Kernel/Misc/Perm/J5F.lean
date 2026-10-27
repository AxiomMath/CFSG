module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5P
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelMisc.CertBind (Bound cert_facts)

theorem hw : szOK 315 9 = true := by quickRfl

theorem hGR : ∀ k < 3, j2FiveGensR[k]! = unpack 315 9 (GR k) := by
  intro k hk
  interval_cases k
  · have e : j2FiveGensR[0]! = CFSG.Monster.B.Co2.Native.hexTable 4 315 (315 * 0)
        CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
      simp [j2FiveGensR, CFSG.Sporadic.Schreier.PairNative.j2StrongArrs,
        CFSG.Sporadic.Schreier.PairNative.j2Strong]
    rw [e, JS.eq]
    exact hexTable_sound JS.all 0 (by norm_num)
  · have e : j2FiveGensR[1]! = CFSG.Monster.B.Co2.Native.hexTable 4 315 (315 * 1)
        CFSG.Sporadic.Schreier.PairNative.j2StrongHex := by
      simp [j2FiveGensR, CFSG.Sporadic.Schreier.PairNative.j2StrongArrs,
        CFSG.Sporadic.Schreier.PairNative.j2Strong]
    rw [e, JS.eq]
    exact hexTable_sound JS.all 1 (by norm_num)
  · have e : j2FiveGensR[2]! = CFSG.Sporadic.SmallOddCore.Native.natArr
        (CFSG.Sporadic.SmallOddCore.Native.hexT 3 315 (315 * 0)
          CFSG.Sporadic.SmallOddCore.j2CentHex) := by
      simp [j2FiveGensR, CFSG.Sporadic.SmallOddCore.j2OuterTbl,
        CFSG.Sporadic.SmallOddCore.j2CentTbl]
    rw [e, JU.eq]
    exact hexT_sound JU.all (by norm_num) 0 (by norm_num)

theorem hLX : ∀ j < 6, j2FiveX j = unpack 315 9 (LX j) := by
  intro j hj
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem hQG : ∀ k < 2, j2FiveQG k = unpack 315 9 (QG k) := by
  intro k hk
  interval_cases k <;> exact arrBind_sound (by quickRfl)

end CertificateChecks.KernelMisc.J2F

end

module

public import CFSG.Sporadic.SmallOddCore.J2CentralizerDInputs
public meta import CFSG.Sporadic.SmallOddCore.J2LocalCheck
public meta import CFSG.Sporadic.Schreier.PairJ2Check
public import Certificates.Kernel.Sporadic.OddCore.J2D2277Check
public import CFSG.Certificates.Kernel.Spor.CntCSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2DCnt

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.MulH
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.SmallOddCore
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem gens_eq : j2DGens.map CFSG.Sporadic.SmallOddCore.Native.natArr = DP.map (unpack 315 9) := by
  have h0 := J2Loc.d_tabs.2 0 (by norm_num)
  have h1 := J2Loc.d_tabs.2 1 (by norm_num)
  have e : j2DGens = [j2DGens.toArray[0]!, j2DGens.toArray[1]!] := rfl
  rw [e, h0.1, h1.1]
  simp only [List.map_cons, List.map_nil, DP, natArr_tabT h0.2, natArr_tabT h1.2]

theorem facts2277 : countW (commW 315 (j2DGens.map CFSG.Sporadic.SmallOddCore.Native.natArr))
    PairJ2.blocks [] = 12 := by
  obtain ⟨hc, hs⟩ := (bAnd_iff (canonL 315 9 DP)
    (Nat.beq (sumN (rcnt (KernelSporSch.PJ2.LR 0)) J2DC.CS) 12)).1 k_small
  rw [gens_eq, PairJ2.blocks, PairJ2.groups, PairJ2.levels,
    cntC3_sound KernelSporSch.PJ2.binds KernelSporSch.PJ2.perm KernelSporSch.PJ2.hl hc J2DC.hk]
  exact Nat.eq_of_beq_eq_true hs

end CertificateChecks.KernelSpor.J2DCnt

end

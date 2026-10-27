module

public import Certificates.Kernel.SporSch.PairBT.McLSylChk
public import Certificates.Kernel.SporSch.PairBT.McLSylZ3
public import CFSG.Sporadic.SmallOddCore.McLWords
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McL2285

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative
open CFSG.Sporadic.Schreier.PairMcL CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.McLSylChk

theorem chainS : ChainS 275 9 PMcL.S PMcL.SI PMcL.LR PMcL.TR PMcL.TRI 13 2 5 PMcL.BP
    mclStrongArrs baseArr PMcLWords.D 18 16 :=
  ⟨PMcLCheck.binds, PMcL.head, PMcL.hl, by norm_num, PMcL.hs⟩

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

theorem clsOK : ClsOK 275 9 McLBT.tA McLBT.tB 2 30000 McLCK := by
  intro j hj
  have hj1 : j < 1 := by simpa [McLCK] using hj
  interval_cases j
  exact ⟨McLCK.h0, elems_of_blocks (by decide) McLCK.hb0, fun i hi => absurd hi (by omega)⟩

theorem hR0 : Nat.beq (McLCK.getD 0 clsD0).R (PMcL.S 0) = true := by quickRfl

theorem dc0 : Nat.beq (McLCK.getD 0 clsD0).c 22275 = true := by quickRfl

theorem rows : Nat.beq (((McLSylZ3.SC.getD 0 []).getD 0 []).sum +
    ((McLSylZ3.SC.getD 1 []).getD 0 []).sum) 22 = true := by quickRfl

theorem lens : Nat.ble (McLCK.getD 0 clsD0).c (((McLSylZ3.SC.getD 0 []).getD 0 []).length * 256)
    = true ∧ Nat.ble (McLCK.getD 0 clsD0).c (((McLSylZ3.SC.getD 1 []).getD 0 []).length * 256) =
    true := ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelSporSch.McL2285

end

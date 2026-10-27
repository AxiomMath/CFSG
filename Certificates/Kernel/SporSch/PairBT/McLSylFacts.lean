module

public import Certificates.Kernel.SporSch.PairBT.McLSylChk
public import Certificates.Kernel.SporSch.PairBT.McLSylZ1
public import Certificates.Kernel.SporSch.PairBT.McLSylZ2
public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.Schreier.PairMcLTotal2Inputs
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLSylFacts

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

theorem clSize : (cl.map fun c => c.2.1.size).sum = 22275 := PMcLCheck.facts.2.2.2.2.2

theorem rows1 : Nat.beq (((McLSylZ1.SC.getD 0 []).getD 0 []).sum +
    ((McLSylZ1.SC.getD 1 []).getD 0 []).sum) 594 = true := by quickRfl

theorem rows2 : Nat.beq (((McLSylZ2.SC.getD 0 []).getD 0 []).sum +
    ((McLSylZ2.SC.getD 1 []).getD 0 []).sum) 22 = true := by quickRfl

theorem len1 : Nat.ble (McLCK.getD 0 clsD0).c (((McLSylZ1.SC.getD 0 []).getD 0 []).length * 256)
    = true ∧ Nat.ble (McLCK.getD 0 clsD0).c (((McLSylZ1.SC.getD 1 []).getD 0 []).length * 256) =
    true := ⟨by quickRfl, by quickRfl⟩

theorem len2 : Nat.ble (McLCK.getD 0 clsD0).c (((McLSylZ2.SC.getD 0 []).getD 0 []).length * 256)
    = true ∧ Nat.ble (McLCK.getD 0 clsD0).c (((McLSylZ2.SC.getD 1 []).getD 0 []).length * 256) =
    true := ⟨by quickRfl, by quickRfl⟩

theorem o12 : ordWK 275 9 bs [PMcL.S 1, PMcL.S 1, PMcL.S 0] 12 = true := by quickRfl
theorem o14 : ordWK 275 9 bs [PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 0] 14 = true := by
  quickRfl
theorem o10 : ordWK 275 9 bs [PMcL.S 1, PMcL.S 1, PMcL.S 1, PMcL.S 0, PMcL.S 1, PMcL.S 1,
    PMcL.S 0, PMcL.S 1, PMcL.S 0] 10 = true := by quickRfl

end CertificateChecks.KernelSporSch.McLSylFacts

end

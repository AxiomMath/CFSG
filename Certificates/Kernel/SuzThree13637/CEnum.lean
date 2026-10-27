module

public import Certificates.Kernel.SuzThree13637.BindSrc
public import Certificates.Kernel.Sporadic.Suz.Chain2306
public import Certificates.Data.Kernel.Spor.RebuildK
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Kernel.B3S3.GenSl
public meta import Certificates.Kernel.SuzThree13637.BindSrc
public meta import Certificates.Kernel.B3S3.GenSl
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

#kb3_enum_sl CFSG.KD.SuzThree13637.CE CFSG.KD.SuzThree13637.cGs CFSG.KD.SuzThree13637.cKeysA
  1782 11 120

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

@[expose] def cBeta (k : Nat) : Array Nat := (#[yTuple, cTuples[0]!, cTuples[1]!])[k]!

@[expose] noncomputable def cReb (k : Nat) : Nat × Nat × Bool :=
  rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => (cBeta k)[l]!) 6

theorem ce_n : Nat.beq CE.N 3240 = true ∧ Nat.beq CE.ng 3 = true := ⟨by quickRfl, by quickRfl⟩

theorem ce_reb : ∀ k < 3, ((cReb k).2.2 && Nat.beq (cReb k).1 (CE.G k) &&
    permB 1782 11 (CE.G k)) = true := by
  intro k hk
  interval_cases k <;> quickRfl

end CFSG.KD.SuzThree13637

end

module

public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuTests
import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.RuEndR
  CFSG.ComponentClassification.RankTwoSporadic.Ru.ruE0RText

#kmisc_hexflat CertificateChecks.KernelSporSch.RuEndR
  CFSG.ComponentClassification.RankTwoSporadic.Ru.ruE0RText 3 4060 12 1

namespace CertificateChecks.KernelSporSch.RuEnd

open CFSG.ComponentClassification.RankTwoSporadic.Ru CFSG.Sporadic.RuSchreier
open CertificateChecks.KernelSporSch

theorem hexAt_eq (b : ByteArray) (o : Nat) : ∀ w,
    CFSG.Monster.B.Max2.Native.hexAt b o w = CFSG.Monster.B.Co2.Native.hexAt b o w
  | 0 => rfl
  | w + 1 => by
    rw [CFSG.Monster.B.Max2.Native.hexAt, CFSG.Monster.B.Co2.Native.hexAt, hexAt_eq b o w]
    rfl

theorem r_eq : ruE0[1]! = CFSG.KS.Raw.unpack 4060 12 (RuEndR.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound RuEndR.all 0 (by norm_num)
  rw [← RuEndR.eq, Nat.mul_zero] at h
  rw [← h]
  simp only [ruE0, ruHexRow, CFSG.Monster.B.Co2.Native.hexTable, ruHexAt, hexAt_eq, Nat.zero_mul,
    Nat.zero_add]
  rfl

end CertificateChecks.KernelSporSch.RuEnd

end

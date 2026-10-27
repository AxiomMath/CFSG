module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeMcLData
public import Certificates.Kernel.Item434.McLK
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeMcLData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelItem434

meta def fiveNM : Array (Array Nat) := #[CFSG.AGLEmbedding.KFactProofs.OrbitsCube.mclFiveNormArr]

end CertificateChecks.KernelItem434

end

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelItem434.F5 CFSG.RankThree.Native.mcl275FiveHex
#kmisc_hexflat CertificateChecks.KernelItem434.F5 CFSG.RankThree.Native.mcl275FiveHex 3 275 9 2
#kmisc_packarrs CertificateChecks.KernelItem434.NH CertificateChecks.KernelItem434.fiveNM 9

public section

namespace CertificateChecks.KernelItem434

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm pw)

@[expose] noncomputable def fiveC : ℕ :=
  cm 275 9 (cm 275 9 (F5.F 0) (F5.F 1))
    (cm 275 9 (pinvS 275 9 (mask 9) (F5.F 0)) (pinvS 275 9 (mask 9) (F5.F 1)))

@[expose] noncomputable def cjA (g y : ℕ) : ℕ := cm 275 9 g (cm 275 9 y (pinvS 275 9 (mask 9) g))

@[expose] noncomputable def fiveW (i j k : ℕ) : ℕ :=
  cm 275 9 (cm 275 9 (pw 275 9 (F5.F 0) i) (pw 275 9 (F5.F 1) j)) (pw 275 9 fiveC k)

theorem kFp : permB 275 9 (F5.F 0) = true ∧ permB 275 9 (F5.F 1) = true ∧
    permB 275 9 (NH 0) = true := ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem kFs : siftM (NH 0) = true := by quickRfl

theorem kFr : Nat.beq fiveC idM = false ∧ Nat.beq (cjA (NH 0) (F5.F 0)) (fiveW 1 2 0) = true ∧
    Nat.beq (cjA (NH 0) (F5.F 1)) (fiveW 1 4 0) = true :=
  ⟨by decide +kernel, by quickRfl, by quickRfl⟩

theorem negF : (!Nat.beq (cjA (NH 0) (F5.F 0)) (fiveW 1 3 0)) = true := by quickRfl

end CertificateChecks.KernelItem434

end

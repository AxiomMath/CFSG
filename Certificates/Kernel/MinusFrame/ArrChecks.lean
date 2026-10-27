module

public import Certificates.Kernel.MinusEnum.Data
public import Certificates.Kernel.MinusFrame.Data
public import Certificates.Data.Kernel.BfsPin

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusFrame
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelMinusEnum

@[expose] noncomputable def pm (p q : ℕ) : ℕ := pcomp 65 7 (mask 7) p q

theorem kFrameCommute : MinusFrame.frameCommuteCheck () = true := by decide +kernel

theorem kNotMemP : allN 65 (fun k => !(Nat.beq (XT 0) (ME.G k))) = true := by decide +kernel

theorem kCentP : allN 65 (fun k => Nat.beq (pm (XT 0) (ME.G k)) (pm (ME.G k) (XT 0)) ==
    centArr.toList.any fun j => j == k) = true := by decide +kernel

theorem kNotMulP : allN 15 (fun a => allN 15 fun b =>
    !(Nat.beq (pm (ME.G centArr[a]!) (ME.G centArr[b]!)) (XT 0))) = true := by decide +kernel

theorem kConjP : (permOK 65 7 (mask 7) (Nat.mul 65 7) (XT 1) (pinvS 65 7 (mask 7) (XT 1)) &&
    !(Nat.beq (pm (pm (XT 1) (XT 0)) (pinvS 65 7 (mask 7) (XT 1))) (XT 0)) &&
    Nat.beq (pm (XT 0) (pm (pm (XT 1) (XT 0)) (pinvS 65 7 (mask 7) (XT 1))))
      (pm (pm (pm (XT 1) (XT 0)) (pinvS 65 7 (mask 7) (XT 1))) (XT 0))) = true := by
  decide +kernel

end CertificateChecks.KernelMinusFrame

end

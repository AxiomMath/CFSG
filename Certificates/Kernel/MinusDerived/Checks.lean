module

public import Certificates.Kernel.MinusDerived.Data
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.Certificates.Kernel.Spor.RawSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin

theorem kNums : (Nat.beq PL.ng 5 && Nat.beq PL.N 7800) = true := by decide +kernel

theorem kBind : (Nat.beq minusLGens.size 5 &&
    allN 5 fun k => bindArrK minusLGens[k]! 65 7 (PL.G k)) = true := by decide +kernel

theorem kPerm : allN 5 (fun k => permOK 65 7 (mask 7) (Nat.mul 65 7) (PL.G k)
    (pinvS 65 7 (mask 7) (PL.G k))) = true := by decide +kernel

@[expose] noncomputable def skL : List ℕ := (List.range 7800).map KL

theorem kK : keysSK 65 7 minusBase PL.N PL.T skL = true := by decide +kernel

end CertificateChecks.KernelMinusL

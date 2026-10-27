module

public import Certificates.Kernel.ONSeven.Defs
public import CFSG.RankThree.Native.ONSevenData

public section

namespace CertificateChecks.KernelSpor.ONR

open CFSG.RankThree.Native CertificateChecks.KernelSpor.ONS

@[expose] def qWords : Array (List Int) := onSevenSylowWords ++ onSevenLineWords

@[expose] def cWords (r : Nat) : Array (List Int) :=
  (onSevenCentWords.getD r #[]).push (onSevenLineWords.getD (onSevenRepIdx.getD r 0) []) ++
    (if r < 3 then onSevenNormalWords.getD r #[] else #[])

@[expose] noncomputable def qF (s : Nat) : Nat → Nat := WW (qWords.getD s [])

@[expose] noncomputable def cF (r s : Nat) : Nat → Nat := WW ((cWords r).getD s [])

@[expose] def kbA : Array Nat := #[0, 1, 2]

end CertificateChecks.KernelSpor.ONR

end

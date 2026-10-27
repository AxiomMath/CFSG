module

public import Certificates.Kernel.OmegaEight.N3MW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage2
  CFSG.EvenSmallLie.OmegaEight.N3Split
  CFSG.EvenSmallLie.OmegaEight.N3Split.MinusW

@[expose] noncomputable def candPN3M (m : ℕ) : Bool :=
  !(enMemK EnN3MC2.D EnN3MC2.m (mul12K m m) && fpowAuxK 64 m 256 ID12 == ID12 &&
      N3Split.Minus.samples.all fun c =>
        enMemK EnN3MC2.D EnN3MC2.m (mul12K (mul12K m c) (fpowAuxK 64 m 255 ID12))) ||
    N3Split.Minus.reps.any fun r => enMemK EnN3MC.D EnN3MC.m (mul12K r.2 m)

theorem candP_eqN3M :
    (fun m => !(candFilter wN3M.c2E N3Split.Minus.samples m) ||
      repOK wN3M.cE N3Split.Minus.reps m) = candPN3M := by
  have hsC : sortedK (decE EnN3MC.D EnN3MC.m).keys = true := (Enum.of_enumOK cE_okN3M).2.1
  have hs2 : sortedK (decE EnN3MC2.D EnN3MC2.m).keys = true := (Enum.of_enumOK c2E_okN3M).2.1
  funext m
  simp only [candFilter, repOK, wN3M, fpowK_eq, mulK_eq, idK_eq,
    memK_decE_eq hsC (by decide +kernel), memK_decE_eq hs2 (by decide +kernel), candPN3M]

end CertificateChecks.KernelO8

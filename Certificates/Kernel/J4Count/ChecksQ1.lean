
module

public import Certificates.Kernel.SporSch.J4S.NoCK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.KC.Enum CFSG.KC.J4Q CertificateChecks.KernelSporSch.J4NoCK

@[expose] def Q1N : Nat := 0x000028098eb9dc8e0e1a1bed674261d9

@[expose] noncomputable def cntQ1 : Nat :=
  cntK 2048 (fun a => Nat.beq (Nat.mod (etaK Q1N a) (Nat.pow 2 112)) Q1N)

theorem fix_q1 : Nat.beq cntQ1 2 = true := by quickRfl

theorem neg_fix_q1 : notB (Nat.beq cntQ1 1) = true := by quickRfl

end CertificateChecks.KernelJ4Count

end

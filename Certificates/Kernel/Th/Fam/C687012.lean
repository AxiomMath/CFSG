module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Data.Th687.MFactsB
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Recog CFSG.Sporadic.Th.Recog.MFactsBData

@[expose] def tT : TE := .word (wJ 6)

@[expose] noncomputable def centP (k : Fin 512) : Bool :=
  Nat.beq ((TE.mul tT (.nf k)).pk thK) ((TE.mul (.nf k) tT).pk thK)

@[expose] noncomputable def centL : List (Fin 512) := (List.finRange 512).filter centP

@[expose] noncomputable def centCK : Bool :=
  centL.all fun k => if k.val = 0 ∨ k.val = 1 then true else centL.any fun k' =>
    Nat.beq ((TE.mul (.nf k) (.nf k')).pk thK) ((TE.mul (.nf k') (.nf k)).pk thK) == false

theorem ok687012a : Nat.beq centL.length 32 = true := by quickRfl

theorem ok687012b : centCK = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end

module

public import Certificates.Kernel.Th.Fam.K
public import Certificates.Data.Th687.MFactsD
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Fam

open CFSG.KC.Th.Expr CFSG.Sporadic.Th.Recog

@[expose] def wjT (i : Fin 8) : TE := .mul (.word (wJ i)) (.pow .a (εJ i))

@[expose] def w1T : TE := .mul (wjT 3) (wjT 4)

@[expose] def w12T : TE := .mul w1T (.mul (.mul (wjT 7) w1T) (.pow (wjT 7) 3))

@[expose] noncomputable def commL (G : Nat) : List (Fin 512) :=
  (List.finRange 512).filter fun k =>
    Nat.beq (thK.mul G ((TE.nf k).pk thK)) (thK.mul ((TE.nf k).pk thK) G)

@[expose] noncomputable def invL (L : List (Fin 512)) : Bool :=
  L.all fun k => decide (k.val ≤ 1) ||
    !Nat.beq ((TE.mul (.nf k) (.nf k)).pk thK) (TE.one.pk thK)

theorem ok687008a : invL (commL (w12T.pk thK)) = true := by quickRfl

theorem ok687008b : invL (commL (w1T.pk thK)) = true := by quickRfl

theorem ok687008c : Nat.beq (commL ((wjT 5).pk thK)).length 8 = true := by quickRfl

end CertificateChecks.KernelTh.Fam

end

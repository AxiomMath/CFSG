module

public import Certificates.Kernel.Sporadic.Fi22.CentData
public import Certificates.Kernel.Sporadic.Fi22.WordKit
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CentS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22CentE
open CFSG.AGLEmbedding.KFactProofs.Fi22Five (signedWord)

@[expose] noncomputable def p24K (v : Nat) : Nat :=
  strictN (Fi22X.c v (Fi22X.c v v)) fun v3 => strictN (Fi22X.c v3 v3) fun v6 =>
    strictN (Fi22X.c v6 v6) fun v12 => Fi22X.c v12 v12

@[expose] noncomputable def cjK (Q : Nat → Nat) (v a : Nat) : Nat :=
  Fi22X.c (Q a) (Fi22X.c v (Q (Nat.sub 5 a)))

@[expose] noncomputable def w1K (Q : Nat → Nat) (v : Nat) : Nat :=
  Fi22X.c (cjK Q v 0) (Fi22X.c (cjK Q v 1) (Fi22X.c (cjK Q v 2) (cjK Q v 3)))

@[expose] noncomputable def w2K (Q : Nat → Nat) (v : Nat) : Nat :=
  Fi22X.c (cjK Q v 0) (Fi22X.c (cjK Q v 0) (Fi22X.c (cjK Q v 1) (cjK Q v 4)))

@[expose] noncomputable def star5K (Q : Nat → Nat) (v : Nat) : Bool :=
  bIf(Nat.beq v (pidn 3510 12), true,
    bIf(Nat.beq (p24K v) (pidn 3510 12),
      bIf(Nat.beq (p24K (w1K Q v)) (pidn 3510 12),
        bIf(Nat.beq (p24K (w2K Q v)) (pidn 3510 12), false, true), true), true))

@[expose] noncomputable def tab6 (Q0 Q1 Q2 Q3 Q4 Q5 : Nat) (a : Nat) : Nat :=
  nIf(Nat.beq a 0, Q0, nIf(Nat.beq a 1, Q1, nIf(Nat.beq a 2, Q2, nIf(Nat.beq a 3, Q3,
    nIf(Nat.beq a 4, Q4, Q5)))))

@[expose] noncomputable def chunkS (j : Nat) : Bool :=
  strictB (Fi22W.W (signedWord wy)) fun Y => strictB (Fi22X.c Y (pidn 3510 12)) fun Y1 =>
    strictB (Fi22X.c Y Y1) fun Y2 => strictB (Fi22X.c Y Y2) fun Y3 =>
      strictB (Fi22X.c Y Y3) fun Y4 => strictB (Fi22X.c Y Y4) fun Y5 =>
        allN 50 (fun t => star5K (tab6 (pidn 3510 12) Y1 Y2 Y3 Y4 Y5) (EK (Nat.add (Nat.mul 50 j) t)))

#kc_each chunkS 0 12

theorem neg : bIf(star5K (fun _ => pidn 3510 12) (EK (pg 10 (mask 10) (NEG 0) 0)), false, true) =
    true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CentS

end

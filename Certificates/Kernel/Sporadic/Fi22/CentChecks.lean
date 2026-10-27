module

public import Certificates.Kernel.Sporadic.Fi22.CentData
public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import Certificates.Data.Kernel.ClosBfs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CentK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.ClosBfs
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22CentE

@[expose] noncomputable def PA (i : Nat) : Nat := pg 10 (mask 10) (TB 0) i
@[expose] noncomputable def LA (i : Nat) : Nat := pg 10 (mask 10) (TB 1) i
@[expose] noncomputable def NX (t : Nat) : Nat := pg 10 (mask 10) (TB 2) t
@[expose] noncomputable def SG (m : Nat) : Nat := pg 10 (mask 10) (TB 3) m

@[expose] noncomputable def KY (i : Nat) : Nat :=
  pg 12 (mask 12) (EK i) 48 + 3510 * (pg 12 (mask 12) (EK i) 752 +
    3510 * (pg 12 (mask 12) (EK i) 788 + 3510 * (pg 12 (mask 12) (EK i) 1425 +
      3510 * (pg 12 (mask 12) (EK i) 847 + 3510 * (pg 12 (mask 12) (EK i) 221 + 3510 * 0)))))


@[expose] noncomputable def nxK (i k : Nat) (e : Nat) : Bool :=
  strictB (NX (Nat.add (Nat.mul i 3) k)) fun t =>
    bAnd(Nat.blt t 600, Nat.beq (EK t) (Fi22X.c (EK (Nat.add 1 k)) e))

@[expose] noncomputable def rowC (i : Nat) : Bool :=
  strictB (EK i) fun e =>
    bAnd(Fi22X.cn e, bAnd(bIf(Nat.beq i 0, true, bAnd(Nat.blt (PA i) i, bAnd(Nat.blt (LA i) 3,
      Nat.beq e (Fi22X.c (EK (Nat.add 1 (LA i))) (EK (PA i)))))),
      bAnd(nxK i 0 e, bAnd(nxK i 1 e, nxK i 2 e))))

@[expose] noncomputable def chunkC (j : Nat) : Bool :=
  allN 10 (fun t => rowC (Nat.add (Nat.mul 10 j) t))

@[expose] noncomputable def keyRow (m : Nat) : Bool :=
  bAnd(Nat.blt (SG m) 600, bIf(Nat.blt m 599, Nat.blt (KY (SG m)) (KY (SG (Nat.succ m))), true))

theorem gen0 : Nat.beq (EK 0) (pidn 3510 12) = true := by quickRfl
theorem gen1 : Nat.beq (EK 1) (Fi22W.W (signedWord wx)) = true := by quickRfl
theorem gen2 : Nat.beq (EK 2) (Fi22W.W (signedWord wy)) = true := by quickRfl
theorem gen3 : Nat.beq (EK 3) (Fi22W.W hw) = true := by quickRfl

#kc_each chunkC 0 60

theorem keys : allN 600 keyRow = true := by quickRfl

theorem bfs : closBfsOK 3 NX PA LA 600 = true := by quickRfl

theorem neg : bAnd(bIf(Nat.beq (EK 5) (Fi22X.c (EK (Nat.add 2 (LA 5))) (EK (PA 5))), false, true),
    bIf(Nat.beq (NX 3) 1, false, true)) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CentK

end

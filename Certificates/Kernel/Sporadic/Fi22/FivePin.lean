module

public import Certificates.Kernel.Sporadic.Fi22.C9554
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Pin

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CFSG.Monster.B.Co2.Native

meta def src : Array (Array Nat) :=
  let a := #[xA, yA, hA, n1A, n2A, zA, g1A, g2A]
  a ++ a.map (invCand 3510)

end CertificateChecks.KernelSpor.Fi22Pin

end

set_option Elab.async false

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22PinT CertificateChecks.KernelSpor.Fi22Pin.src 12

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Pin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W
open CertificateChecks.KernelSpor.Fi22C9554

@[expose] noncomputable def pin (k : Nat) : Nat := Fi22PinT k

@[expose] noncomputable def e8 (X Y H N1 N2 Z A B k : Nat) : Nat :=
  bif Nat.blt k 6 then six X Y H N1 N2 Z k else two A B (k - 6)

@[expose] noncomputable def pinK (T : Nat → Nat) (X Y H N1 N2 Z A B : Nat) : Bool :=
  allN 16 (fun k => Fi22X.cn (T k)) &&
    allN 8 (fun k => permOK 3510 12 (mask 12) (3510 * 12) (T k) (T (k + 8))) &&
    allN 8 (fun k => Nat.beq (T k) (e8 X Y H N1 N2 Z A B k)) &&
    allN 8 (fun k => Nat.beq (T (k + 8)) (Fi22X.inv (T k)))

@[expose] noncomputable def allPin : Bool :=
  strictB (W (signedWord wx)) fun X => strictB (W (signedWord wy)) fun Y =>
  strictB (W hw) fun H => strictB (W nw1) fun N1 => strictB (W nw2) fun N2 =>
  strictB (W zw) fun Z =>
  strictB (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g1w) fun A =>
  strictB (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g2w) fun B =>
    pinK pin X Y H N1 N2 Z A B

theorem ok : allPin = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22Pin

end

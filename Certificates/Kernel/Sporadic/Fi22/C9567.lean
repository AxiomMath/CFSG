module

public import Certificates.Kernel.Sporadic.Fi22.C9554
public import Certificates.Kernel.Sporadic.Fi22.FiveK
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveThreeData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C9567

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W
open CertificateChecks.KernelSpor.Fi22C9554 CertificateChecks.KernelSpor.Fi22FiveK

@[expose] noncomputable def core (X Y H N1 N2 Z A B AI BI EA EB : Nat) : Bool :=
  allN 6 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (six X Y H N1 N2 Z j)
      (Fi22X.inv (six X Y H N1 N2 Z j))) &&
    allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (two A B j) (two AI BI j)) &&
    Fi22X.cn EA && Fi22X.cn EB &&
    Nat.beq (pwK EA 3) (pidn 3510 12) && Nat.beq (pwK EB 3) (pidn 3510 12) &&
    Nat.beq (Fi22X.c EA EB) (Fi22X.c EB EA) &&
    (Nat.beq EA (pidn 3510 12) == false) && (Nat.beq EB (pidn 3510 12) == false) &&
    (Nat.beq EB EA == false) && (Nat.beq EB (pwK EA 2) == false) &&
    allN 3 (fun i => allN 3 fun j => (i == 0 && j == 0) ||
      (Nat.beq (Fi22X.c (pwK EA i) (pwK EB j)) (pidn 3510 12) == false))

@[expose] noncomputable def all9567 : Bool :=
  strictB (W (signedWord wx)) fun X => strictB (W (signedWord wy)) fun Y =>
  strictB (W hw) fun H => strictB (W nw1) fun N1 => strictB (W nw2) fun N2 =>
  strictB (W zw) fun Z =>
  strictB (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g1w) fun A =>
  strictB (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g2w) fun B =>
  strictB (Fi22X.inv A) fun AI => strictB (Fi22X.inv B) fun BI =>
  strictB (wd (two A B) (two AI BI) e9W1) fun EA => strictB (wd (two A B) (two AI BI) e9W2) fun EB =>
    core X Y H N1 N2 Z A B AI BI EA EB

theorem ok : all9567 = true := by quickRfl

theorem lettersE : bAnd(lettersK 2 e9W1, lettersK 2 e9W2) = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22C9567

end

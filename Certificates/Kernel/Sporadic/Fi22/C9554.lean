module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public import Certificates.Data.Kernel.OrbChain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C9554

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.OrbChain
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22W

@[expose] noncomputable def wd (PS PSI : Nat → Nat) (w : List Int) : Nat :=
  wordK 3510 12 (mask 12) (pidn 3510 12) PS PSI w

@[expose] noncomputable def six (X Y H N1 N2 Z k : Nat) : Nat :=
  bif Nat.beq k 0 then X else bif Nat.beq k 1 then Y else bif Nat.beq k 2 then H else
    bif Nat.beq k 3 then N1 else bif Nat.beq k 4 then N2 else Z

@[expose] noncomputable def two (A B k : Nat) : Nat := bif Nat.beq k 0 then A else B

@[expose] noncomputable def lt8 (A B C D AI BI CI DI k : Nat) : Nat :=
  bif Nat.blt k 4 then
    (bif Nat.beq k 0 then A else bif Nat.beq k 1 then B else bif Nat.beq k 2 then C else D)
  else
    (bif Nat.beq k 4 then AI else bif Nat.beq k 5 then BI else bif Nat.beq k 6 then CI else DI)

@[expose] def hLet (l : Int) : Nat := bif decide (0 < l) then l.toNat + 1 else (-l).toNat + 5

@[expose] def ws9554 : List (List Nat) :=
  [[0], [1], [2], [3]] ++ (hchainW.toList.drop 2).map fun x => x.map hLet

@[expose] def bs9554 : List Nat := [0, 85, 86, 162, 102, 401, 1440, 457]

@[expose] noncomputable def core (X Y H N1 N2 Z A B C D AI BI CI DI : Nat) : Bool :=
  allN 6 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (six X Y H N1 N2 Z j)
      (Fi22X.inv (six X Y H N1 N2 Z j))) &&
    allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (two A B j) (two AI BI j)) &&
    permOK 3510 12 (mask 12) (3510 * 12) C CI && permOK 3510 12 (mask 12) (3510 * 12) D DI &&
    chainOK 12 (lt8 A B C D AI BI CI DI) 3510 4 ws9554 bs9554 8000 1045094400

@[expose] noncomputable def all9554 : Bool :=
  strictB (W (signedWord wx)) fun X => strictB (W (signedWord wy)) fun Y =>
  strictB (W hw) fun H => strictB (W nw1) fun N1 => strictB (W nw2) fun N2 =>
  strictB (W zw) fun Z =>
  strictB (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g1w) fun A =>
  strictB (wd (six X Y H N1 N2 Z) (fun k => Fi22X.inv (six X Y H N1 N2 Z k)) g2w) fun B =>
  strictB (Fi22X.inv A) fun AI => strictB (Fi22X.inv B) fun BI =>
  strictB (wd (two A B) (two AI BI) h1w) fun C => strictB (wd (two A B) (two AI BI) h2w) fun D =>
  strictB (Fi22X.inv C) fun CI => strictB (Fi22X.inv D) fun DI =>
    core X Y H N1 N2 Z A B C D AI BI CI DI

theorem ok : all9554 = true := by quickRfl

theorem lettersG : bAnd(lettersK 6 g1w, lettersK 6 g2w) = true := by quickRfl

theorem lettersH : bAnd(lettersK 2 h1w, lettersK 2 h2w) = true := by quickRfl

end CertificateChecks.KernelSpor.Fi22C9554

end

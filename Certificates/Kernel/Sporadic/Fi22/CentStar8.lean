module

public import Certificates.Kernel.Sporadic.Fi22.CentStar
public import Certificates.Kernel.Sporadic.Fi22.FiveK
meta import Certificates.Kernel.Sporadic.Fi22.CentData
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CentT

meta def neg8M : Array (Array Nat) :=
  #[#[((List.range Fi22CentE.eM.size).find? fun i => 0 < i &&
    CFSG.Monster.B.Co2.Native.eqA 3510
      (CFSG.Sporadic.FischerOddCore.Native.powA 3510 Fi22CentE.eM[i]! 8)
      (CFSG.Monster.B.Co2.Native.idA 3510)).getD 0]]

end CertificateChecks.KernelSpor.Fi22CentT

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CentT.NEG8 CertificateChecks.KernelSpor.Fi22CentT.neg8M 10

namespace CertificateChecks.KernelSpor.Fi22CentT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22CentE
open CertificateChecks.KernelSpor.Fi22CentS
open CFSG.AGLEmbedding.KFactProofs.Fi22Five (signedWord hw uw)

@[expose] noncomputable def st8K (Q : Nat → Nat) (v a b : Nat) : Nat :=
  Fi22FiveK.pwK (Fi22X.c (Fi22FiveK.pwK (cjK Q v a) 7) (cjK Q v b)) 8

@[expose] noncomputable def starK (Q : Nat → Nat) (v : Nat) : Bool :=
  Nat.beq v (pidn 3510 12) || !(Nat.beq (Fi22FiveK.pwK v 8) (pidn 3510 12)) ||
    (List.range 5).any fun a => (List.range 5).any fun b =>
      !(Nat.beq (st8K Q v a b) (pidn 3510 12))

@[expose] noncomputable def bp (t : Nat) : Nat :=
  nIf(Nat.beq t 0, 0, nIf(Nat.beq t 1, 1, nIf(Nat.beq t 2, 2, nIf(Nat.beq t 3, 3,
    nIf(Nat.beq t 4, 6, 4)))))

@[expose] noncomputable def ap (X p : Nat) : Nat := pg 12 (mask 12) X p

@[expose] noncomputable def itP (f : Nat → Nat) (k p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ acc => f acc) k

@[expose] noncomputable def cjP (Q : Nat → Nat) (v a p : Nat) : Nat :=
  ap (Q a) (ap v (ap (Q (Nat.sub 5 a)) p))

@[expose] noncomputable def st8P (Q : Nat → Nat) (v a b p : Nat) : Nat :=
  itP (fun x => itP (cjP Q v a) 7 (cjP Q v b x)) 8 p

@[expose] noncomputable def movesB (f : Nat → Nat) : Bool :=
  !(allN 6 fun t => strictB (bp t) fun p => Nat.beq (f p) p)

@[expose] noncomputable def starB (Q : Nat → Nat) (v : Nat) : Bool :=
  Nat.beq v (pidn 3510 12) || movesB (itP (ap v) 8) ||
    (List.range 5).any fun a => (List.range 5).any fun b => movesB (st8P Q v a b)

@[expose] noncomputable def starAllK : Bool :=
  strictB (Fi22W.W (signedWord wy)) fun Y => strictB (Fi22X.c Y (pidn 3510 12)) fun Y1 =>
    strictB (Fi22X.c Y Y1) fun Y2 => strictB (Fi22X.c Y Y2) fun Y3 =>
      strictB (Fi22X.c Y Y3) fun Y4 => strictB (Fi22X.c Y Y4) fun Y5 =>
        allN 600 (fun t => starB (tab6 (pidn 3510 12) Y1 Y2 Y3 Y4 Y5) (EK t))

theorem starAll : starAllK = true := by quickRfl

@[expose] noncomputable def gensK : Bool :=
  strictB (Fi22W.W (signedWord wx)) fun X => strictB (Fi22W.W hw) fun H =>
    strictB (Fi22X.c Fi22X.GO (Fi22W.W uw)) fun U =>
      Fi22X.cn H && Fi22X.cn U && Fi22X.cn X && Fi22X.cn (Fi22W.W uw) &&
        Nat.beq (Fi22X.c H X) (Fi22X.c X H) && Nat.beq (Fi22X.c U X) (Fi22X.c X U) &&
        !(Fi22X.siftP U)

theorem gens : gensK = true := by quickRfl

theorem neg : (Fi22X.siftP (Fi22W.W uw) &&
    !(starB (fun _ => pidn 3510 12) (EK (pg 10 (mask 10) (NEG8 0) 0)))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi22CentT

end

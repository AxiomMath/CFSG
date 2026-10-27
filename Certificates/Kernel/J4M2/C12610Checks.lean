module

public import Certificates.Kernel.J4M2.C12611Checks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClassData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KC.J4Slp
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.Sporadic.J4Schreier

@[expose] noncomputable def threeR : List Nat :=
  runK c rm one (threeProg.map instrCode) (initKN one A A B Bi 140)

@[expose] noncomputable def threeT (E EI G GI : List Nat) : Bool :=
  andB (Nat.beq (getN 0 E 0) one) (andB
    ((List.range 27).all fun k => (List.range 27).all fun l =>
      CFSG.KC.J4Slp.strictB (mulJ c rm (getN 0 E k) (getN 0 E l)) fun p =>
        (List.range 27).any fun m => Nat.beq p (getN 0 E m))
    (andB ((List.range 27).all fun k => (List.range 27).any fun m => Nat.beq (getN 0 EI k) (getN 0 E m))
      (andB ((List.range 27).all fun k => (List.range 27).all fun l =>
          orB (Nat.beq k l) (neK rm (getN 0 E k) (getN 0 E l)))
        ((List.range 27).all fun k => orB (Nat.beq k 0)
          (Nat.beq (mulJ c rm (mulJ c rm (getN 0 G k) (getN 0 E k)) (getN 0 GI k)) CE)))))

@[expose] noncomputable def colK (R : List Nat) (o i : Nat) : List Nat :=
  (List.range 27).map fun k => getN 0 R (2 * (o + k) + i)

@[expose] noncomputable def threeK (R : List Nat) : Bool :=
  forceB (colK R 70 0) fun E => forceB (colK R 70 1) fun EI =>
    forceB (colK R 110 0) fun G => forceB (colK R 110 1) fun GI => threeT E EI G GI

theorem c12610lt : threeProg.all (CFSG.Sporadic.GLQ.Instr.lt threeN) = true := by quickRfl

theorem c12610run : forceB threeR threeK = true := by quickRfl

end CertificateChecks.KernelJ4Gam

end

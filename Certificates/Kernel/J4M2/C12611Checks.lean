module

public import Certificates.Data.Kernel.J4SlpB
public import Certificates.Kernel.J4M2.C12607Checks
public import Certificates.Kernel.J4M2.KDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0GenData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4C0pKData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KC.J4Slp
  CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.Sporadic.J4Schreier

@[expose] noncomputable def CE : Nat := pk cEr

@[expose] noncomputable def l0R : List Nat :=
  runK c rm one (l0Prog.map instrCode) (initKN one A A B Bi 170)

@[expose] noncomputable def eltK (R : List Nat) (r p : Nat) : Bool :=
  CFSG.KC.J4Slp.strictB (regM R r) fun x =>
    andB (Nat.beq (mulJ c rm x Z0) (mulJ c rm Z0 x))
      (andB (Nat.beq (mulJ c rm x CE) (mulJ c rm CE x))
        (andB (Nat.beq (powJ c rm one x p) one) (neK rm x one)))

@[expose] noncomputable def l0K (R : List Nat) : Bool :=
  andB (eltK R 160 7) (andB (eltK R 161 7) (andB (eltK R 162 11) (andB (eltK R 163 11)
    (andB (Nat.beq (powJ c rm one (mulJ c rm (regM R 160) (regM R 161)) 7) Z0)
      (Nat.beq (powJ c rm one (mulJ c rm (regM R 162) (regM R 163)) 11) Z0)))))

theorem c12611cE : (rowsOK cEr && Nat.beq CE CertificateChecks.KernelJ4M2.cK &&
    Nat.beq (mulJ c rm CE (mulJ c rm CE CE)) one) = true := by quickRfl

theorem c12611lt : l0Prog.all (CFSG.Sporadic.GLQ.Instr.lt l0N) = true := by quickRfl

theorem c12611run : forceB l0R l0K = true := by quickRfl

end CertificateChecks.KernelJ4Gam

end

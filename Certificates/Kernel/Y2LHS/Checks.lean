module

public import Certificates.Kernel.Y2LHS.Words
public import Certificates.Data.Kernel.TabMat
public import Certificates.Kernel.VecCert.HS
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelY2LHS

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.HS
  CFSG.Sporadic.HS.Native CFSG.OddStandard.HigherRank.G2Three.Sec2
  CFSG.Sporadic.Recognition.CoverRecipe

theorem words_eq : y2l_hsW () = y2lGws.map natWord := by decide +kernel

theorem tabK : tabMatK (hsData ()).d NA NAi NB NBi (y2lGws.map natWord)
    (y2lPairs.map fun q => (natWord q.1, natWord q.2)) = true := by
  quickRfl

theorem sevenK : ((y2l_ws7 2).map (y2l_subst (y2l_hsW ()))).all (fun v =>
    (List.range 1100).any fun x =>
      !Nat.beq (vmF (hsData ()).d (matW (hsData ()).d NA NAi NB NBi v) (lk Pt 32 x)) (lk Pt 32 x)) =
    true := by
  quickRfl

end CertificateChecks.KernelY2LHS

end

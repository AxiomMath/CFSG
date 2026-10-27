module

public import Certificates.Data.Kernel.TabMat
public import Certificates.Kernel.VecCert.HS
public import Certificates.Kernel.HSMult.Pairs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CertificateChecks.KernelHSMult

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.HS
  CFSG.Sporadic.HS.Native CFSG.Sporadic.Recognition.HSMultiplier CFSG.Sporadic.Recognition.CoverRecipe

theorem hseed : seedK csA csB (hsData ()).d MA MB NA NB (hsData ()).expA (hsData ()).expB = true := by
  quickRfl

theorem hn : andB (Nat.blt (nat_lit 0) (hsData ()).n) (Nat.blt (hsData ()).n (pw2 (nat_lit 30))) = true := by
  quickRfl

theorem hP0 : Nat.beq (lk Pt (nat_lit 32) (nat_lit 0)) (hsData ()).v0 = true := by quickRfl

theorem hAi : Nat.beq (mulF (hsData ()).d NA NAi) (idF (hsData ()).d) = true := by quickRfl

theorem hBi : Nat.beq (mulF (hsData ()).d NB NBi) (idF (hsData ()).d) = true := by quickRfl

theorem tabK : tabMatK (hsData ()).d NA NAi NB NBi (hsGenWords.map natWord)
    (hsPairs.map fun q => (natWord q.1, natWord q.2)) = true := by
  quickRfl

end CertificateChecks.KernelHSMult

end

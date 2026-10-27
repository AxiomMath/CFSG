module

public import Certificates.Kernel.Tc.M24Src
public import Certificates.Data.Kernel.TcK
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Kernel.Tc.M24Src
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThreeCore.M24
public meta import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.Native.FiveKit
public meta import CFSG.RankThree.Native.FiveKit
public import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Sporadic.Schreier.M24

set_option maxRecDepth 400000

#kb3_enum CertificateChecks.KernelTc.M24.EQ CertificateChecks.KernelTc.M24.gQ
  CertificateChecks.KernelTc.M24.keys 24 5
#kb3_enum CertificateChecks.KernelTc.M24.EK CertificateChecks.KernelTc.M24.gK
  CertificateChecks.KernelTc.M24.keys 24 5
#kb3_enum CertificateChecks.KernelTc.M24.EC CFSG.AGLEmbeddingD2.Wilson.Census219.m24caA
  CertificateChecks.KernelTc.M24.keys 24 5
#kb3_enum CertificateChecks.KernelTc.M24.EY CFSG.AGLEmbeddingD2.Wilson.Census219.m24sA
  CertificateChecks.KernelTc.M24.keys 24 5
#kmisc_packarrs CertificateChecks.KernelTc.M24.MS CertificateChecks.KernelTc.M24.misc 5
#kb3_enum CertificateChecks.KernelTc.M24.ES CertificateChecks.KernelTc.M24.sig
  CertificateChecks.KernelTc.M24.keys6 6 3

public section

namespace CertificateChecks.KernelTc.M24

open CFSG.AGLEmbeddingD2.Wilson.Census219 CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K CFSG.KC.TcK

@[expose] def sigF (i j : Nat) : Nat := (sig[i]!)[j]!

theorem bMS : ∀ j < 11, arrBind misc[j]! 24 5 (MS j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bQ : ∀ j < 2, arrBind gQ[j]! 24 5 (EQ.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bK : ∀ j < 3, arrBind gK[j]! 24 5 (EK.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bC : ∀ j < 2, arrBind m24caA[j]! 24 5 (EC.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bY : ∀ j < 2, arrBind m24sA[j]! 24 5 (EY.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bS : ∀ j < 2, arrBind sig[j]! 6 3 (ES.G j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem ns : Nat.beq EQ.ng 2 = true ∧ Nat.beq EK.ng 3 = true ∧ Nat.beq EC.ng 2 = true ∧
    Nat.beq EY.ng 2 = true ∧ Nat.beq ES.ng 2 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem gperm : allN 2 (fun k => permB 24 5 (EQ.G k)) = true ∧
    allN 3 (fun k => permB 24 5 (EK.G k)) = true ∧ allN 2 (fun k => permB 24 5 (EC.G k)) = true ∧
    allN 2 (fun k => permB 24 5 (EY.G k)) = true ∧ allN 2 (fun k => permB 6 3 (ES.G k)) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem rest : tcRestK 24 5 6 (MS 10) 2 EQ.G MS (fun i => MS (Nat.add 2 i)) 3 EK.G
    (fun j => MS (Nat.add 4 j)) sigF EQ.N EQ.T EK.N EK.T ES.N = true := by
  quickRfl

theorem inC : allN 2 (fun l => CFSG.KC.TcK.memK EC.N EC.T (EQ.G l)) = true := by quickRfl

theorem nY : Nat.beq EY.N 27 = true := by quickRfl

theorem cubeY : allN EY.N (fun k => Nat.beq (pw 24 5 (EY.T k) 3) (pidn 24 5)) = true := by
  quickRfl

theorem restNeg : (!tcRestK 24 5 6 (MS 10) 2 EQ.G MS (fun i => MS (Nat.add 2 i)) 3 EK.G
    (fun j => MS (Nat.add 4 (Nat.sub j (Nat.ble j 1).toNat))) sigF EQ.N EQ.T EK.N EK.T
    ES.N) = true := by
  quickRfl

end CertificateChecks.KernelTc.M24

end

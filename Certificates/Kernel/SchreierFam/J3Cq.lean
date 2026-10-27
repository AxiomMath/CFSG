module

public import Certificates.Kernel.Sporadic.J3K.Data
public import Certificates.Kernel.Sporadic.RawGenSplit
public import Certificates.Kernel.Sporadic.ON.Gen
public import Certificates.Data.Kernel.SchreierFam.All3
public import Certificates.Data.Kernel.SchreierFam.CqK
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.WordChunk
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.ClassicalInvolution.J3Data CFSG.Monster.B.Co2.Native

meta def aM : Array Nat := abArr[0]!
meta def bM : Array Nat := abArr[1]!
meta def aiM : Array Nat := abInv[0]!
meta def biM : Array Nat := abInv[1]!
meta def k0M : Array Nat := kStrong[0]!
meta def k1M : Array Nat := kStrong[1]!
meta def ki0M : Array Nat := kInv[0]!
meta def ki1M : Array Nat := kInv[1]!

meta def sufM (j i : Nat) : Array Nat := wordA 20520 abArr abInv (kWordsAB[j]!.drop i)

meta def v0aM : Array Nat := sufM 0 17
meta def v0bM : Array Nat := sufM 0 34
meta def v0cM : Array Nat := sufM 0 51
meta def v1aM : Array Nat := sufM 1 17
meta def v1bM : Array Nat := sufM 1 34
meta def v1cM : Array Nat := sufM 1 51

end CertificateChecks.KernelSchreierFam.J3Cq

#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.A 15 CertificateChecks.KernelSchreierFam.J3Cq.aM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.B 15 CertificateChecks.KernelSchreierFam.J3Cq.bM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.AI 15 CertificateChecks.KernelSchreierFam.J3Cq.aiM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.BI 15 CertificateChecks.KernelSchreierFam.J3Cq.biM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.K0 15 CertificateChecks.KernelSchreierFam.J3Cq.k0M
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.K1 15 CertificateChecks.KernelSchreierFam.J3Cq.k1M
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.KI0 15
  CertificateChecks.KernelSchreierFam.J3Cq.ki0M
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.KI1 15
  CertificateChecks.KernelSchreierFam.J3Cq.ki1M
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.V0a 15
  CertificateChecks.KernelSchreierFam.J3Cq.v0aM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.V0b 15
  CertificateChecks.KernelSchreierFam.J3Cq.v0bM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.V0c 15
  CertificateChecks.KernelSchreierFam.J3Cq.v0cM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.V1a 15
  CertificateChecks.KernelSchreierFam.J3Cq.v1aM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.V1b 15
  CertificateChecks.KernelSchreierFam.J3Cq.v1bM
#ks_perm CertificateChecks.KernelSchreierFam.J3Cq.V1c 15
  CertificateChecks.KernelSchreierFam.J3Cq.v1cM

public section

namespace CertificateChecks.KernelSchreierFam.J3Cq

@[expose] def sD : List (List Int) := []

end CertificateChecks.KernelSchreierFam.J3Cq

#ks_rawchain_sl2_data CertificateChecks.KernelSchreierFam.J3Cq.SY 20520 15 0 16
  CFSG.ClassicalInvolution.J3Data.sStrong CFSG.ClassicalInvolution.J3Data.sBase 4
  CertificateChecks.KernelSchreierFam.J3Cq.sD

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KC.Misc.ArrEnum CFSG.KS.SchreierFam
  CFSG.KS.SporSch CertificateChecks.KernelSpor.J3K CFSG.ClassicalInvolution.J3Data

@[expose] noncomputable def AB (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), A, B)

@[expose] noncomputable def ABI (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), AI, BI)

@[expose] noncomputable def KK (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), K0, K1)

@[expose] noncomputable def KKI (h : Nat) : Nat := nIf(Nat.beq h (nat_lit 0), KI0, KI1)

@[expose] noncomputable def V0 (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), K0,
    nIf(Nat.beq i (nat_lit 17), V0a, nIf(Nat.beq i (nat_lit 34), V0b, V0c)))

@[expose] noncomputable def V1 (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), K1,
    nIf(Nat.beq i (nat_lit 17), V1a, nIf(Nat.beq i (nat_lit 34), V1b, V1c)))

@[expose] noncomputable def k0Ch (c : Nat) : Bool :=
  chunkK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[0]! 17 V0 (c * 17)

@[expose] noncomputable def k1Ch (c : Nat) : Bool :=
  chunkK 20520 15 (mask 15) (pidn 20520 15) AB ABI kWordsAB[1]! 17 V1 (c * 17)

@[expose] def cqWords : List (List Nat) := [[0], [0, 0]]

@[expose] noncomputable def cqSl (L : List (List Nat)) (a : Nat) : Bool :=
  allN (rcnt (SY.LR 1)) fun b => allN (rcnt (SY.LR 2)) fun c =>
    cqK 20520 15 A KK L (pcomp 20520 15 (mask 15)
      (pcomp 20520 15 (mask 15) (trAt 20520 (20520 * 15) SY.LR SY.TR 0 a)
        (trAt 20520 (20520 * 15) SY.LR SY.TR 1 b))
      (trAt 20520 (20520 * 15) SY.LR SY.TR 2 c))

@[expose] noncomputable def cqS (a : Nat) : Bool := cqSl cqWords a

theorem a_pmk : Nat.beq A (pmk 20520 15 (r32 TA)) = true := by quickRfl

theorem b_pmk : Nat.beq B (pmk 20520 15 (r32 TB)) = true := by quickRfl

theorem a_perm : permB 20520 15 A = true := by quickRfl

theorem b_perm : permB 20520 15 B = true := by quickRfl

theorem ai_eq : Nat.beq AI (pinvS 20520 15 (mask 15) A) = true := by quickRfl

theorem bi_eq : Nat.beq BI (pinvS 20520 15 (mask 15) B) = true := by quickRfl

end CertificateChecks.KernelSchreierFam.J3Cq

#kon_slices CertificateChecks.KernelSchreierFam.J3Cq.k0Ch 0 4
#kon_join CertificateChecks.KernelSchreierFam.J3Cq.k0All
  CertificateChecks.KernelSchreierFam.J3Cq.k0Ch 4
#kon_slices CertificateChecks.KernelSchreierFam.J3Cq.k1Ch 0 4
#kon_join CertificateChecks.KernelSchreierFam.J3Cq.k1All
  CertificateChecks.KernelSchreierFam.J3Cq.k1Ch 4

namespace CertificateChecks.KernelSchreierFam.J3Cq

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SchreierFam CFSG.KS.SporSch
  CFSG.ClassicalInvolution.J3Data

theorem ki0_eq : Nat.beq KI0 (pinvS 20520 15 (mask 15) K0) = true := by quickRfl

theorem ki1_eq : Nat.beq KI1 (pinvS 20520 15 (mask 15) K1) = true := by quickRfl

theorem s0_eq :
    Nat.beq (SY.S 0) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[0]!) = true := by
  quickRfl

theorem s1_eq :
    Nat.beq (SY.S 1) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[1]!) = true := by
  quickRfl

theorem s2_eq :
    Nat.beq (SY.S 2) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[2]!) = true := by
  quickRfl

theorem s3_eq :
    Nat.beq (SY.S 3) (wordK 20520 15 (mask 15) (pidn 20520 15) KK KKI sWordsK[3]!) = true := by
  quickRfl

theorem rc0 : Nat.beq (rcnt (SY.LR 0)) 128 = true := by quickRfl

theorem cqNeg1 : cqSl [[0]] 3 = false := by decide +kernel

theorem cqNeg0 : cqSl [] 3 = false := by decide +kernel

end CertificateChecks.KernelSchreierFam.J3Cq

#kon_slices CertificateChecks.KernelSchreierFam.J3Cq.cqS 0 128
#kon_join CertificateChecks.KernelSchreierFam.J3Cq.cqSAll
  CertificateChecks.KernelSchreierFam.J3Cq.cqS 128

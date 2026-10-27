module

public import Certificates.Kernel.SporSch.Mathieu.GenOddPt
public import Certificates.Kernel.LocalQT.He4148.Glue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Range.Basic
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSchreierFam

open CFSG.KS.SporSch.MOCG CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

meta def SXA : Array (Array Nat) := strongOf 35 heThreeSigmaA.toArray heThreeChainWordsA

meta def baseXA : Array Nat := #[0, 1, 2, 3]

meta def SXB : Array (Array Nat) := strongOf 8 heThreeSigmaB.toArray heThreeChainWordsB

meta def baseXB : Array Nat := #[1, 0, 2]

end CertificateChecks.KernelSchreierFam

#ks_rawchain CertificateChecks.KernelSchreierFam.XAQ 35 6 16
  CertificateChecks.KernelSchreierFam.SXA CertificateChecks.KernelSchreierFam.baseXA 4
  CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeChainWordsA

#ks_rawchain CertificateChecks.KernelSchreierFam.XBQ 8 4 8
  CertificateChecks.KernelSchreierFam.SXB CertificateChecks.KernelSchreierFam.baseXB 4
  CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He.heThreeChainWordsB

namespace CertificateChecks.KernelSchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.PrimCert

theorem bXA : bindsK 35 6 XAQ.S XAQ.SI heThreeSigmaA 0 = true := by quickRfl

theorem bXB : bindsK 8 4 XBQ.S XBQ.SI heThreeSigmaB 0 = true := by quickRfl

theorem oXA : Nat.beq (ordK XAQ.LR 4) 2520 = true := by quickRfl

theorem oXB : Nat.beq (ordK XBQ.LR 3) 168 = true := by quickRfl

theorem primA_12637K : primOK 35 heThreeLettersA heThreeTwA heThreeEwA = true := by
  decide +kernel

theorem primB_12637K : primOK 8 heThreeLettersB heThreeTwB heThreeEwB = true ∧
    fourOK 8 heThreeLettersB heThreeFourB = true := by
  constructor <;> decide +kernel

theorem neg_12637K : Nat.beq (ordK XBQ.LR 3) 336 = false ∧
    fourOK 8 heThreeLettersB [] = false := by
  constructor <;> decide +kernel

theorem len_XA : heThreeSigmaA.length = 4 := rfl

theorem len_XB : heThreeSigmaB.length = 4 := rfl

theorem atXA {j : Nat} (hj : j < 4) :
    BindAt 35 6 (XAQ.S j) (XAQ.SI j) (heThreeSigmaA.getD j #[]) := by
  have h := bindsK_spec bXA j (by rw [len_XA]; exact hj)
  rwa [Nat.zero_add] at h

theorem atXB {j : Nat} (hj : j < 4) :
    BindAt 8 4 (XBQ.S j) (XBQ.SI j) (heThreeSigmaB.getD j #[]) := by
  have h := bindsK_spec bXB j (by rw [len_XB]; exact hj)
  rwa [Nat.zero_add] at h

theorem chainXA : ChainK 35 6 (heThreeSigmaA.map (permOrId 35)) heThreeChainWordsA
    (#v[0, 1, 2, 3] : Vector (Fin 35) 4) XAQ.S XAQ.SI XAQ.LR XAQ.TR XAQ.TRI 8 XAQ.BP 3 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, XAQ.head, XAQ.hl,
    by norm_num, XAQ.hs⟩
  have hj' : j < heThreeSigmaA.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atXA (len_XA ▸ hj'))

theorem chainXB : ChainK 8 4 (heThreeSigmaB.map (permOrId 8)) heThreeChainWordsB
    (#v[1, 0, 2] : Vector (Fin 8) 3) XBQ.S XBQ.SI XBQ.LR XBQ.TR XBQ.TRI 6 XBQ.BP 1 8 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, XBQ.head, XBQ.hl,
    by norm_num, XBQ.hs⟩
  have hj' : j < heThreeSigmaB.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atXB (len_XB ▸ hj'))

theorem xa_check : heThreeXA.check = true ∧ heThreeXA.orderCertificate = 2520 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainXA
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oXA)⟩

theorem xb_check : heThreeXB.check = true ∧ heThreeXB.orderCertificate = 168 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainXB
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oXB)⟩

end CertificateChecks.KernelSchreierFam

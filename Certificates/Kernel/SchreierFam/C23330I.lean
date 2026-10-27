module

public import Certificates.Kernel.SporSch.Mathieu.GenOddPt
public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Data.SolMaxHeGen
public meta import Certificates.Data.SolMaxHeGen
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.Range.Basic
import all Init.Data.Nat.Fold
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CertificateChecks.KernelSchreierFam

open CFSG.KS.SporSch.MOCG CFSG.ComponentClassification.SolMax.HeGen

meta def SK23330 : Array (Array Nat) := strongOf 240 (wK.map kA).toArray kWords

meta def baseK23330 : Array Nat := #[0, 1, 2]

end CertificateChecks.KernelSchreierFam

#ks_rawchain CertificateChecks.KernelSchreierFam.KQ 240 8 16
  CertificateChecks.KernelSchreierFam.SK23330 CertificateChecks.KernelSchreierFam.baseK23330 3
  CFSG.ComponentClassification.SolMax.HeGen.kWords

namespace CertificateChecks.KernelSchreierFam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148
open CFSG.ComponentClassification.SolMax.HeGen CFSG.Monster.B.Co2.Native
open CFSG.Certificates CFSG.Sporadic.Schreier

theorem bK23330 : bindsK 240 8 KQ.S KQ.SI (wK.map kA) 0 = true := by quickRfl

theorem oK23330 : Nat.beq (ordK KQ.LR 3) 40320 = true := by quickRfl

theorem len_K23330 : (wK.map kA).length = 3 := rfl

theorem atK23330 {j : Nat} (hj : j < 3) :
    BindAt 240 8 (KQ.S j) (KQ.SI j) ((wK.map kA).getD j #[]) := by
  have h := bindsK_spec bK23330 j (by rw [len_K23330]; exact hj)
  rwa [Nat.zero_add] at h

theorem chainK23330 : ChainK 240 8 ((wK.map kA).map (permOrId 240)) kWords
    (#v[0, 1, 2] : Vector (Fin 240) 3) KQ.S KQ.SI KQ.LR KQ.TR KQ.TRI 6 KQ.BP 15 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, KQ.head, KQ.hl,
    by norm_num, KQ.hs⟩
  have hj' : j < (wK.map kA).length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atK23330 (len_K23330 ▸ hj'))

theorem heGenK_check : heGenK.check = true ∧ heGenK.orderCertificate = 40320 := by
  have e : heGenK = certificate (by decide) ((wK.map kA).map (permOrId 240)) kWords
      (#v[0, 1, 2] : Vector (Fin 240) 3) (by decide) := by
    rw [heGenK, List.map_map]
    rfl
  rw [e]
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainK23330
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oK23330)⟩

theorem innerArr_23330K : (heInnerSigma0.all (permChk 240) && lettersOK 9 wX5 &&
    wK.all (lettersOK 9) && permChk 240 x5A &&
    wK.all (fun w => permChk 240 (sWord w) && permChk 240 (kA w)) &&
    eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A)))) (idA 240) &&
    !eqA 240 x5A (idA 240)) = true := by
  decide +kernel

theorem innerNeg_23330K :
    eqA 240 (compA 240 x5A (compA 240 x5A (compA 240 x5A x5A))) (idA 240) = false := by
  decide +kernel

theorem heGenInner_23330 : heGenInnerCheck = true := by
  rw [heGenInnerCheck, heGenK_check.1, heGenK_check.2]
  simpa using innerArr_23330K

end CertificateChecks.KernelSchreierFam

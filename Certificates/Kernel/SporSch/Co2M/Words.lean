
module

public import Certificates.Kernel.SporSch.Co2M.WordsBase

public import Certificates.Kernel.SporSch.Co2M.Class
public import Certificates.Kernel.SporSch.Co2M.ChainS
public import Certificates.Kernel.SporSch.Co2M.OrbC
public import Certificates.Kernel.SporSch.Co2M.OrbD
public import Certificates.Kernel.SporSch.Co2M.OrbJ
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
meta import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier

end CertificateChecks.KernelSporSch.Co2M

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

theorem words_check : wordsCheck localRec levelsS = true := by
  have hm := mat_ok
  simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨hzz, htt⟩, hz0⟩, ht0⟩, hzm⟩, htm⟩, hcz⟩, hdt⟩ := hm
  have jRep := repT_append cRep dRep
  have jlen : (cT ++ dT).length = 4 := by rw [List.length_append, cT_len, dT_len]
  unfold wordsCheck
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', CFSG.Monster.B.Co2.allLt_iff,
    and_assoc]
  refine ⟨allInv_of_repT aRep, allInv_of_repT cInitRep, allInv_of_repT dRep,
    allInv_of_repT dStarRep, allInv_of_repT rRep, allInv_of_repT cRep, allInv_of_repT cStarRep,
    allInv_of_repT qRep, allInv_of_repT sRep, isInvA_rep wRep, isInvA_rep hRep, aArrs_size, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cInitRep.1, cInitT_len]
  · rw [dRep.1, dT_len]
  · rw [dStarRep.1, dStar_len]
  · rw [rRep.1, rT_len]
  · rw [cRep.1, cT_len]
  · rw [cStarRep.1, cStar_len]
  · rw [qRep.1, qT_len]
  · rw [sRep.1, sT_len]
  · intro k hk
    exact orig_eqA Co2LC.shapeOK.2.2.2.1 Co2LC.binds hk (by norm_num)
      (repT_get cRep (by rw [cT_len]; exact hk)) (allN_spec orig_c k hk)
  · intro k hk
    exact orig_eqA Co2LD.shapeOK.2.2.2.1 Co2LD.binds hk (by norm_num)
      (repT_get dRep (by rw [dT_len]; exact hk)) (allN_spec orig_d k hk)
  · intro k hk
    exact orig_eqA Co2LS.shapeOK.2.2.2.1 Co2LS.binds hk (by norm_num)
      (repT_get sRep (by rw [sT_len]; exact hk)) (allN_spec orig_s k hk)
  · intro k hk
    exact orig_eqA Co2LJ.shapeOK.2.2.2.1 Co2LJ.binds hk (by norm_num)
      (repT_get jRep (by rw [jlen]; exact hk)) (allN_spec orig_j k hk)
  · intro k hk
    exact sift_of (repT_get qRep (by rw [qT_len]; exact hk)) (allN_spec bind_q k hk)
      (allN_spec sift_q k hk)
  · intro k hk
    exact sift_of (repT_get rRep (by rw [rT_len]; exact hk)) (allN_spec bind_r k hk)
      (allN_spec sift_r k hk)
  · exact sift_of rep_ztP0 (allN_spec bind_e 0 (by norm_num)) (allN_spec sift_e 0 (by norm_num))
  · exact sift_of rep_ztP1 (allN_spec bind_e 1 (by norm_num)) (allN_spec sift_e 1 (by norm_num))
  · have h := (rep_cmp zRep zRep).1
    rw [Nat.eq_of_beq_eq_true hzz, ← idA_eq] at h
    rw [h]
    exact eqA_self _ _
  · have h := (rep_cmp tRep tRep).1
    rw [Nat.eq_of_beq_eq_true htt, ← idA_eq] at h
    rw [h]
    exact eqA_self _ _
  · exact ne_of_mat zRep hz0 hzm
  · exact ne_of_mat tRep ht0 htm
  · intro k hk
    have hk' : k < cT.length := by rw [cT_len]; exact hk
    exact eqA_of_mat (rep_cmp (repT_get cRep hk') zRep) (rep_cmp zRep (repT_get cRep hk'))
      (Nat.eq_of_beq_eq_true (allN_spec hcz k hk))
  · intro k hk
    have hk' : k < dT.length := by rw [dT_len]; exact hk
    exact eqA_of_mat (rep_cmp (repT_get dRep hk') tRep) (rep_cmp tRep (repT_get dRep hk'))
      (Nat.eq_of_beq_eq_true (allN_spec hdt k hk))

end CertificateChecks.KernelSporSch.Co2M

end

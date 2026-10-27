module

public import CFSG.Certificates.Kernel.TwoNodeSmall.PosBKSound
import Certificates.Kernel.TwoNodeSmall.PosBChecks
import Certificates.Kernel.TwoNodeSmall.PosBOrd
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs
public import Certificates.Kernel.TwoNodeSmall.PosBData

namespace CFSG.KD.TNS708601

#kc_forall_chunks allG (fun k => CFSG.KD.TNS708601.cg k = true) 63
  CFSG.KD.TNS708601.ch708601.g_ 1
#kc_forall_chunks allO (fun k => CFSG.KD.TNS708601.co k = true) 153
  CFSG.KD.TNS708601.ch708601.o_ 1

theorem allN : (CFSG.TwoNodeSmall.PosBK.ochunks oB os).length = nO := by
  have h := ch708601.n_0
  rw [cn.eq_1] at h
  exact Nat.eq_of_beq_eq_true h

theorem allG' : ∀ g < 63, CFSG.TwoNodeSmall.PosBK.grpIdxB rk os g = true := allG

theorem allO' : ∀ i < nO, CFSG.TwoNodeSmall.PosBK.ochunkB oB os i = true := allO

theorem oB_pos : 0 < oB := Nat.zero_lt_succ 11

public section

public theorem posB_closed_all :
    ∀ Q ∈ CFSG.TwoNodeSmall.posBPts (), ∀ [Fact Q.pt.p.Prime], Q.ClosedPosB :=
  CFSG.TwoNodeSmall.PosBK.posB_closed_of oB_pos allG' allN allO'

end

end CFSG.KD.TNS708601

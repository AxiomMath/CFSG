module

public import Certificates.Kernel.SporSch.Tits.Five10050E
public import Certificates.Kernel.SporSch.Tits.Five10050K
public import Certificates.Kernel.SporSch.Tits.Inv2266
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.RankThree.PartOne.KE
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsAbel

theorem f_eq : titsFiveArr = unpack 1755 11 TitsF := by
  unfold titsFiveArr
  rw [wa_eq fW, Nat.eq_of_beq_eq_true fB]

theorem sFH : siftA 1755 (rawLevels 1755 titsHArrs (baseArr 1755 titsHBase)) (baseArr 1755 titsHBase)
    0 (unpack 1755 11 TitsF) = true :=
  siftK_soundR bindsH permH TitsH.hl rfl (hi_of cF) (range_of_canonK cF) kFH

theorem agrFH : Agrees TitsH.LR TitsH.TR PFH (fun a => commA a titsFiveArr) :=
  fun t0 t1 t2 t3 t4 h => by
    rw [f_eq]
    exact baseCommG_eq bindsH TitsH.head TitsH.hl (NS := 220) (CH := 8) (by norm_num) TitsH.hs
      TitsInv.ndH h cF sFH

theorem propsF : (∀ x ∈ titsCH5, isInvA 1755 x (invCand 1755 x) = true ∧ inH x = true) ∧
    titsCH5.Pairwise (fun a b => eqA 1755 a b = false) :=
  surv5K_propsT (fun a => commA a titsFiveArr) bindsH permH TitsH.hl

theorem pow5 : eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 titsFiveArr titsFiveArr)
    titsFiveArr) titsFiveArr) titsFiveArr) (idA 1755) = true := by
  rw [f_eq, cu cF cF, cu (cc cF cF) cF, cu (cc (cc cF cF) cF) cF,
    cu (cc (cc (cc cF cF) cF) cF) cF, TitsCentral.id_eq,
    eqA_unpack (cc (cc (cc (cc cF cF) cF) cF) cF) TitsCentral.canId]
  exact kF5

theorem facts : lettersOK 13 titsFiveWord = true ∧ inH titsFiveArr = true ∧
    eqA 1755 titsFiveArr (idA 1755) = false ∧
    eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 titsFiveArr titsFiveArr)
      titsFiveArr) titsFiveArr) titsFiveArr) (idA 1755) = true ∧
    all5 1755 titsHLevels (fun a => !commA a titsFiveArr || anyEq titsCH5 a) = true ∧
    titsCH5.length = 10 ∧
    titsCH5.all (fun c => isInvA 1755 c (invCand 1755 c) && commA c titsFiveArr && inH c) = true ∧
    titsCH5.Pairwise (fun a b => eqA 1755 a b = false) := by
  refine ⟨by decide, siftK_soundR bindsH permH TitsH.hl f_eq (hi_of cF) (range_of_canonK cF) kFH,
    ?_, pow5, all5_surv _ _, ?_, ?_, propsF.2⟩
  · rw [f_eq]
    exact neIdK_sound kFne
  · exact (surv5K_countT bindsH permH TitsH.hl agrFH TitsHFE.all).trans
      (Nat.eq_of_beq_eq_true cntF)
  · rw [List.all_eq_true]
    intro c hc
    have hq : commA c titsFiveArr = true := TitsInv.mem_surv (q := fun a => commA a titsFiveArr) hc
    obtain ⟨h1, h2⟩ := propsF.1 c hc
    rw [h1, hq, Bool.true_and, Bool.true_and]
    exact h2

end CertificateChecks.KernelSporSch.TitsFive

end

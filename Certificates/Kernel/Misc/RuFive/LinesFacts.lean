module

public import Certificates.Kernel.Misc.RuFive.Lines
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.FiveLocKSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.FiveLocK CFSG.RankThree.Native
open CFSG.RankThree.PartOne

theorem line_eq {j : Nat} (hj : j < 31) : ruFiveLines[j]! = unpack 4060 12 (L j) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound RF.all (j + 2) (show j + 2 < 33 by omega)
  rw [← RF.eq] at h
  unfold ruFiveLines
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  exact h

theorem permL' {j : Nat} (hj : j < 31) : permB 4060 12 (L j) = true := allN_spec permL j hj

theorem comm_eq {j k : Nat} (hj : j < 31) (hk : k < 31) :
    commA 4060 ruFiveLines[j]! ruFiveLines[k]! = commK 4060 12 (L j) (L k) := by
  rw [line_eq hj, line_eq hk]
  exact commA_unpack szOK' (permL' hj) (permL' hk)

theorem lines : CFSG.EvenSporadicStandard.RuStd.S2.ruFiveLinesCheck = true := by
  unfold CFSG.EvenSporadicStandard.RuStd.S2.ruFiveLinesCheck
  rw [Bool.and_eq_true, comm_eq (by norm_num) (by norm_num)]
  refine ⟨kComm, ?_⟩
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro j hj
  have hj' := allN_spec kLines j hj
  unfold lineAt at hj'
  rw [comm_eq hj (by norm_num)]
  cases hr : Nat.beq (Nat.mod (ruFiveRec.getD j 0) 31) 0
  · have hne : (ruFiveRec.getD j 0 % 31 != 0) = true := by
      rw [bne_iff_ne]
      exact fun e => by
        change Nat.mod (ruFiveRec.getD j 0) 31 = 0 at e
        rw [e] at hr
        exact absurd hr (by decide)
    rw [hne]
    rfl
  · rw [hr] at hj'
    dsimp only at hj'
    have he : (ruFiveRec.getD j 0 % 31 != 0) = false := by
      rw [bne_eq_false_iff_eq]
      exact Nat.eq_of_beq_eq_true hr
    rw [he, Bool.false_or]
    cases hc : commK 4060 12 (L j) (L 1)
    · rfl
    · rw [hc] at hj'
      dsimp only at hj'
      rw [Bool.not_true, Bool.false_or]
      exact beq_iff_eq.2 (Nat.eq_of_beq_eq_true hj')

end CertificateChecks.KernelMisc.RuFive

end

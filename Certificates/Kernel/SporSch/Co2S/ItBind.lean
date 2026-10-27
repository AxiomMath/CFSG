module

public import Certificates.Kernel.SporSch.Co2S.ItT
public import Certificates.Kernel.SporSch.Co2S.ItRecord
public import CFSG.Certificates.Kernel.SporSch.FixKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2t

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.Co2It

theorem dArrs_size : dArrs.size = 2 := by
  simp [dArrs, len]

theorem dArrs_get (j : Nat) (hj : j < 2) : dArrs[j]! = unpack 2300 12 (Co2tD j) := by
  have hw : wordA 2300 aArrs (rawInvs 2300 aArrs) (localRec.dWords.getD j []) =
      unpack 2300 12 (Co2tD j) := by
    refine (wordEqK_sound (kS := 2) ⟨aArrs_size, fun k hk => aArrs_get k hk⟩
      (allN_of_forall fun k hk => perm_hd k hk) ?_).1
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · exact wd0
    · exact wd1
  rw [← hw, dArrs, getElem!_pos _ j (by simp [len]; omega)]
  simp [wordArr, List.getElem?_eq_getElem (by rw [len]; omega : j < localRec.dWords.length)]

theorem tArr_eq : tArr = unpack 2300 12 (Co2tT 0) :=
  (wordEqK_sound (kS := 2) ⟨dArrs_size, dArrs_get⟩ pd wt).1

theorem itList_eq : itList = co2ItNat := by
  rw [itList, tArr_eq]
  exact fixK_sound fx

theorem facts :
    itList.length = 140 ∧ orbitRecordOK itList 1024650 (co3KeySearch aArrs itList 1024650) = true :=
  ⟨by rw [itList_eq]; rfl, by rw [itList_eq]; exact record⟩

end CertificateChecks.KernelSporSch.Co2t

end

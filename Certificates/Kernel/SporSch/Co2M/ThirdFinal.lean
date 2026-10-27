
module

public import Certificates.Kernel.SporSch.Co2M.ThirdFinalBase

public import Certificates.Kernel.SporSch.Co2M.ThirdBound
public import CFSG.Certificates.Kernel.SporSch.ThirdLowerPrelude
public import CFSG.Certificates.Kernel.SporSch.ThirdLower
public import CFSG.Certificates.Kernel.SporSch.ThirdDfs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

theorem thirdCheckK
    (hE : ECheckH) :
    thirdCheck (thirdLevels witRec) witRec.third.baseIndices.toArray uArr
      (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr = true := by
  have hT : ThirdFactsH := thirdFactsK
  have hcard : Nat.card locH3 = 1474560 := le_antisymm card_locH3_leK (le_card_locH3 hE)
  have hd : (dfsCnt thL thB uArr 12 13 0 (idA 2300) == 1474560) = true := by
    rw [dfsCnt_eq_card hT locU_ne_one, hcard]
    rfl
  unfold thirdCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨hT.base_size, hT.base_lt⟩, hT.L_size⟩, hT.sizes⟩, hT.tr⟩, hT.u_inv⟩, hT.u_fix⟩, hd⟩

end CertificateChecks.KernelSporSch.Co2M

end

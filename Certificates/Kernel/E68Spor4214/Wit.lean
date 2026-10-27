module

public import Certificates.Kernel.E68Spor4214.Final
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporCen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS

public section

namespace CFSG.KD.E68S4214

open CFSG.Quasithin.E6.Spor CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.HS
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_wit
    (z₀ : J hsData) (hzT : (tab hsData.n z₀).toArray = hsSLP[164]!) :
    (¬ ∀ g : J hsData, g * z₀ = z₀ * g) ∧ RWit hsCtx z₀ 5 15 := by
  have : FaithfulSMul (J hsData) (Fin hsData.n) :=
    faithfulSMul_of_base (base_lt hs_facts) (base_property hs_facts)
  have hsT : hsCtx.D.sTabs = hsSTabs := hsCtx.hsg.symm.trans hs_sGens.1
  obtain ⟨hr, hnc⟩ := hs_ok
  have hnc2 : ncChk hsData.n hsCtx.ta hsSLP[164]! = true := hnc
  have h1 := not_central_of_ncChk (n := hsData.n) hsCtx.ha hzT hnc2
  have h2 : RWit hsCtx z₀ 5 15 := rChk_sound hsCtx hsT hzT (by norm_num) hr
  exact ⟨h1, h2⟩

end CFSG.KD.E68S4214

end

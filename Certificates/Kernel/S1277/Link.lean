module

public import Certificates.Kernel.S1277.ModFacts
public import Certificates.Kernel.S1277.Lat
public import CFSG.Certificates.Kernel.S1277KCandSound

public section

namespace CFSG.KP.S1277Link

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277Struct CFSG.Quasithin.H13.I1277
  CFSG.KS.S1277Lat CFSG.KS.S1277Cand CFSG.KP.S1277Mod CFSG.KP.S1277Lat CFSG.KD.S1277Mod

variable {G : Type} [Group G] {K : Subgroup G} {κ : G → ℕ}

theorem mcod_g (hκ : KCod K (mkTab (stabL gm6 5)) κ) : MCod K Mg κ := mcod_of_kcod modFacts_gm6 hκ

theorem mcod_n (hκ : KCod K (mkTab (stabL nm6 5)) κ) : MCod K Mn κ := mcod_of_kcod modFacts_nm6 hκ

theorem zc_g : (mkTab (stabL gm6 5)).idB * 64 + 5 = oneg * 64 + 5 := by rw [modFacts_gm6.idB]

theorem zc_n : (mkTab (stabL nm6 5)).idB * 64 + 5 = onen * 64 + 5 := by rw [modFacts_nm6.idB]

end CFSG.KP.S1277Link

end

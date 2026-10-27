module

public import Certificates.Kernel.S1277.Gm
public import CFSG.Certificates.Kernel.S1277KGmSound

public section

namespace CFSG.KP.S1277Gm

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277Gm CFSG.KS.S1277Gm CFSG.KD.S1277Gm

theorem gmList_eq : gmList = gmIdx.map Mc.ofIdx := by
  rw [gmList_eq_gmK]
  exact eq_of_eqMc _ _ gmK_ok

theorem gm6_eq : gm6 = gm6P.map B6.ofP := by
  rw [gm6, gmList_eq]
  exact eq_of_eqB6 _ _ gm6P_ok

theorem nm6_eq : nm6 = gm6P.map B6.ofP ++ (gm6P.map B6.ofP).map (·.comp sig6) := by
  rw [nm6, gm6_eq]

theorem orbit5_card : (gm6.map fun B => B.app 5).toFinset.card = 45 := by
  rw [gm6_eq]
  exact (orb_of_orbChk _ orbChk_ok).1

theorem orbit45 (c : ℕ) (hc : c < 64) (h : (gm6.map fun B => B.app c).toFinset.card = 45) :
    ∃ B ∈ gm6, B.app 5 = c := by
  rw [gm6_eq] at h ⊢
  exact (orb_of_orbChk _ orbChk_ok).2 c hc h

theorem orbitSize_gm6 (c : ℕ) :
    Certificates.Data.S1277MLine.orbitSize gm6 c = (gm6.map fun B => B.app c).toFinset.card :=
  orbitSize_eq_card gm6 c

end CFSG.KP.S1277Gm

end

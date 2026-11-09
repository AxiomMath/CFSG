module

public import Certificates.Kernel.LocalQT.Base.C4060H
public import Certificates.Kernel.LocalQT.Base.C4060P
public import CFSG.Certificates.Kernel.LocalQTRankOSound

public section

namespace CFSG.KD.LQT.C4060

open CFSG.KC.LQT.RB CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2
open CFSG.Sporadic.HS.Native (hsData)

theorem cert : RankCert.RankCertS hsData.n hsB (slpTabsA hsTa hsTb hsProg) hsQp 4 hsEnum.1
    hsEnum.2.1 hsEnum.2.2 9 := by
  unfold hsEnum hsSLP
  rw [C4140.n_eq, C4140.ta_eq, C4140.tb_eq]
  have hq : ∀ i < 2 ^ 9, rowRQ 9 3 (2 ^ 9) PT CT MQT i = true := by
    intro i hi
    have hi' : i < 512 := hi
    have h8 : i / 64 < 8 := by omega
    have h := CFSG.KC.LQT.RW.Pf.allR_true (Q.all (i / 64) h8) (i % 64)
      (Nat.mod_lt _ (by norm_num))
    have e : Nat.mul (i / 64) 64 + i % 64 = i := by
      change i / 64 * 64 + i % 64 = i
      omega
    rwa [e] at h
  have he : ∀ x < 512, eqvRU 9 3 512 CT MQT TUPT TUIT x = true := by
    intro i hi
    have h8 : i / 64 < 8 := by omega
    have h := CFSG.KC.LQT.RW.Pf.allR_true (EQ.all (i / 64) h8) (i % 64)
      (Nat.mod_lt _ (by norm_num))
    have e : Nat.mul (i / 64) 64 + i % 64 = i := by
      change i / 64 * 64 + i % 64 = i
      omega
    rwa [e] at h
  have hz := ZQ.all 0 (by norm_num)
  change CFSG.KC.Ord.andB _ _ = true at hz
  rw [CFSG.KC.LQT.BW.Pf.andB_eq, Bool.and_eq_true, CFSG.KC.LQT.BW.Pf.lenA_eq] at hz
  have hp := rankBQ_of_rankBO (d := 3) (zi := 10) (K := 87) (L := 1) (by norm_num) hq he
    (by norm_num) (by norm_num) (Nat.eq_of_beq_eq_true hz.2) (Nat.le_of_ble_eq_true hz.1)
    (fun j hj => P.all j hj)
  exact rankBQ_sound (by norm_num) _ _ _ _ _ _ 3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd hq (by norm_num) hp

end CFSG.KD.LQT.C4060

end

module

public import Certificates.Kernel.ReflExt.Checks708606a
public import Certificates.Kernel.ReflExt.Checks708606b
public import CFSG.Certificates.Kernel.ReflExt.NineKSound
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

namespace CFSG.KD.NK708606

#kc_forall_chunks all606 (fun k => CFSG.KD.NK708606.cn k = true) 40 CFSG.KD.NK708606.ch708606.f_ 1

open CFSG.NineAll CFSG.ReflExt.NK CFSG.TwoNodeSmall.WitK

public section

theorem nine_frame8 : ∃ T, verifyAllN (nineFrame8 ()) nineBstab T = true :=
  partN_verify _ _ (nthK fd0 fr 0) fun i hi => by
    have h := all606 i (Nat.lt_of_lt_of_le hi (by decide))
    simp only [cn, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi] at h
    exact h

theorem nine_frame9 : ∃ T, verifyAllN (nineFrame9 ()) nineBstab T = true :=
  partN_verify _ _ (nthK fd0 fr 1) fun i hi => by
    have h := all606 (20 + i) (Nat.lt_of_lt_of_le (by omega : 20 + i < 40) (by decide))
    have hd : (20 + i) / 20 = 1 := by omega
    have hm : (20 + i) % 20 = i := by omega
    simp only [cn, hd, hm] at h
    exact h

end

end CFSG.KD.NK708606

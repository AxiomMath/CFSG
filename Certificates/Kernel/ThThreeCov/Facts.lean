module

public import Certificates.Kernel.ThThreeCov.Chk
public import Certificates.Kernel.Th.Fam.Ctx
public import CFSG.Certificates.Kernel.ThThreeCov.Sound
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelThThreeCov

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.KC.Th CFSG.KC.ThThreeCov CFSG.KD.ThThreeCov
  CertificateChecks.KernelTh.Fam CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp CFSG.StandardType.SporadicShape
  CFSG.HardMathSupport.Dickson.Sec6.Up34Th

#kc_forall_tree ch1023506Dall (fun c => ch1023506D c = true) 14
  CertificateChecks.KernelThThreeCov.ch1023506D

#kc_forall_tree ch1023506Tall (fun j => ch1023506T j = true) 81
  CertificateChecks.KernelThThreeCov.ch1023506T

theorem defs_len : lenR defs = 221 := beq_t (andB_t ch1023506L).1

theorem defs0 : defs.getD 0 [] = [] := by decide +kernel

theorem sim3 : simOK defs psi0 6 ThThreeNative.prog3 = true := by decide +kernel

theorem simU : simOK defs psi0 38 TabThNative.progU = true := by decide +kernel

theorem neg1023506_sim : simOK defs psi0 7 ThThreeNative.prog3 = false := by decide +kernel

theorem neg1023506_simU :
    simOK defs psi0 38 (TabThNative.progU.set 2 (.pow 5 2 4)) = false := by decide +kernel

theorem map3 : simMap psi0 6 ThThreeNative.prog3 11 = 34 := by decide +kernel

theorem mapU : simMap psi0 38 TabThNative.progU 22 = 58 := by decide +kernel

theorem defs54 : defs.getD 54 [] =
    (CFSG.Sporadic.Th.Native.abWord CFSG.Sporadic.Th.Native.x1Str).map abL := by decide +kernel

theorem defs55 : defs.getD 55 [] =
    (CFSG.Sporadic.Th.Native.abWord CFSG.Sporadic.Th.Native.x2Str).map abL := by decide +kernel

theorem defs56 : defs.getD 56 [] = (List.replicate 9 [59, 60]).flatten := by decide +kernel

theorem reps : (cls.getD 0 (0, [], [], [])).1 = 34 ∧ (cls.getD 1 (0, [], [], [])).1 = 61 ∧
    (cls.getD 2 (0, [], [], [])).1 = 58 := by decide +kernel

theorem cover1023506 :
    SporKRestCover 3 J := by
  obtain ⟨g, hR, ga, gb, gx, gy, hg⟩ := regs_sound thCtx ch1023506S
    (defs_all (by rw [defs_len]; norm_num) ch1023506Dall)
  have hdef : ∀ i < defs.length, g (5 + i) = ((defs.getD i []).map g).prod :=
    fun i hi => hg i (by rw [lenR_eq]; exact hi)
  have h5 : g 5 = 1 := by
    rw [hdef 0 (by rw [← lenR_eq, defs_len]; norm_num), defs0]
    rfl
  have hn : tb + 81 ≤ 5 + lenR defs := Nat.le_of_ble_eq_true (andB_t ch1023506G).1
  have hn3 : 3 < 5 + lenR defs := by omega
  have hT := tab_sound thCtx hR ch1023506G ch1023506Tall
  have hA : ClassGen (fun j => g (tb + j)) (g (cls.getD 0 (0, [], [], [])).1) :=
    cls_sound thCtx hR gx gy hn hn3 ch1023506I ch1023506C0
  have hB : ClassGen (fun j => g (tb + j)) (g (cls.getD 1 (0, [], [], [])).1) :=
    cls_sound thCtx hR gx gy hn hn3 ch1023506I ch1023506C1
  have hC : ClassGen (fun j => g (tb + j)) (g (cls.getD 2 (0, [], [], [])).1) :=
    cls_sound thCtx hR gx gy hn hn3 ch1023506I ch1023506C2
  obtain ⟨r0, r1, r2⟩ := reps
  rw [r0] at hA
  rw [r1] at hB
  rw [r2] at hC
  have lS : g 34 = thS := by
    rw [thS, slp_link hdef ga gb h5 sim3, map3]
  have lU : g 58 = thU := by
    rw [thU, slp_link hdef ga gb h5 simU, mapU]
  have lZ : g 61 = thZ :=
    z_link hdef ga gb (by rw [← lenR_eq, defs_len]; norm_num) defs54 defs55 defs56
  rw [lS] at hA
  rw [lZ] at hB
  rw [lU] at hC
  exact cover_of hT hA hB hC

end CertificateChecks.KernelThThreeCov

end

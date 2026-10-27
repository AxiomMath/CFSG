module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.OrbitData
public import Certificates.Kernel.ThBfs.OrbChk
public import CFSG.Certificates.Kernel.ThBfs.Sound
import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CertificateChecks.KernelThBfs

open CFSG.KC.Misc.Clos CFSG.KC.ThBfs CFSG.EvenSporadicStandard.ThStd.LocalDataTh

noncomputable def decY3 (e : ℕ) : Y3 := (Fin.ofNat 256 e, Fin.ofNat 256 (e / 256), Fin.ofNat 256 (e / 65536))

theorem decY3_inj {a b : ℕ} (ha : a < 16777216) (hb : b < 16777216) (h : decY3 a = decY3 b) :
    a = b := by
  simp only [decY3, Prod.mk.injEq, Fin.ext_iff, Fin.val_ofNat] at h
  omega

theorem imgTab_B1c : imgTab B1c = (List.range 256).map (orbImg 0) := by decide +kernel

theorem imgTab_B2c : imgTab B2c = (List.range 256).map (orbImg 1) := by decide +kernel

theorem imgFin_map {k : ℕ} {cs : List ℕ} (h : imgTab cs = (List.range 256).map (orbImg k))
    (c : Fin 256) : imgFin (imgTab cs) c = Fin.ofNat 256 (orbImg k c.val) := by
  unfold imgFin
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.isLt]
  rfl

theorem orbImg_lt (k c : ℕ) : orbImg k c < 256 := Nat.mod_lt _ (by norm_num)

theorem decY3_orbAct' {k : ℕ} {cs : List ℕ} (h : imgTab cs = (List.range 256).map (orbImg k))
    (e : ℕ) : decY3 (orbAct e k) =
      (imgFin (imgTab cs) (decY3 e).1, imgFin (imgTab cs) (decY3 e).2.1,
        imgFin (imgTab cs) (decY3 e).2.2) := by
  rw [imgFin_map h, imgFin_map h, imgFin_map h]
  have ha := orbImg_lt k (e % 256)
  have hb := orbImg_lt k (e / 256 % 256)
  have hc := orbImg_lt k (e / 65536 % 256)
  have hact : orbAct e k = orbImg k (e % 256) + (256 * orbImg k (e / 256 % 256) +
      65536 * orbImg k (e / 65536 % 256)) := rfl
  simp only [decY3, Fin.val_ofNat, hact]
  generalize orbImg k (e % 256) = a at ha ⊢
  generalize orbImg k (e / 256 % 256) = b at hb ⊢
  generalize orbImg k (e / 65536 % 256) = c at hc ⊢
  refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;>
    simp only [Fin.val_ofNat] <;> omega

theorem decY3_orbAct (e k : ℕ) (hk : k < [mapX, mapY].length) :
    decY3 (orbAct e k) = [mapX, mapY][k] (decY3 e) := by
  rcases k with _ | _ | k
  · exact decY3_orbAct' imgTab_B1c e
  · exact decY3_orbAct' imgTab_B2c e
  · simp at hk

theorem orbAt_all : ∀ i < 22680, bfsAt orbAct 16777216 [mapX, mapY].length 22680 OR OC OS i = true :=
  forall_of_chunks 1260 18 orbAt fun c hc => by
    interval_cases c
    exacts [ch24201_r0, ch24201_r1, ch24201_r2, ch24201_r3, ch24201_r4, ch24201_r5, ch24201_r6,
      ch24201_r7, ch24201_r8, ch24201_r9, ch24201_r10, ch24201_r11, ch24201_r12, ch24201_r13,
      ch24201_r14, ch24201_r15, ch24201_r16, ch24201_r17]

theorem orbitList_length : orbitList.length = 22680 := by
  have h0 : decY3 (keyAt OR 0) = rootY3 := by
    rw [ch24201_root]
    rfl
  rw [orbitList, bfsAt_sound [mapX, mapY] decY3 (fun e _ k hk => decY3_orbAct e k hk)
    (fun a ha b hb h => decY3_inj ha hb h) (by norm_num) orbAt_all h0 (by norm_num)]
  simp

end CertificateChecks.KernelThBfs

end

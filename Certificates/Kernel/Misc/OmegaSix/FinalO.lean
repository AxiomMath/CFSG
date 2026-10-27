module

public import CFSG.Certificates.Kernel.Misc.OmegaSixOSound
public import Certificates.Kernel.Misc.OmegaSix.FinalC
public import Certificates.Kernel.Misc.OmegaSix.HeadO
public import Certificates.Kernel.Misc.OmegaSix.ChecksO
public import Certificates.Kernel.Misc.OmegaSix.ChecksP
public import Certificates.Kernel.Misc.OmegaSix.ChecksR
public import Certificates.Kernel.Misc.OmegaSix.ChecksW

public section

namespace CFSG.KD.OmegaSix

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.CaseIIClassAux CFSG.KC.OmegaSix
  CFSG.KC.Misc.Spec CFSG.KD.YamakiRepF CFSG.KD.YamakiRep

theorem oMatC : a6cMat = matF (RO 5) := by
  rw [a6cMat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatD1 : a6d1Mat = matF (RO 6) := by
  rw [a6d1Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatD2 : a6d2Mat = matF (RO 7) := by
  rw [a6d2Mat.eq_1, matF]
  congr 1
  decide +kernel

theorem oMatAO : aMat = matF (ROO 0) := by
  rw [oGen0]
  exact oMatA

theorem oMatBO : bMat = matF (ROO 1) := by
  rw [oGen1]
  exact oMatB

theorem oMatRO : rMat = matF (ROO 2) := by
  rw [oGen2]
  exact oMatR

theorem oLtR : ROO 2 < 2 ^ 36 := by
  rw [oGen2]
  exact oHdrLt 2 (by norm_num)

theorem oTabO : ∀ q < 203, chunkF3 ROO (rstG ROO 0) 3 51840 256 q = true := by
  intro q hq
  by_cases h : q < 102
  · have e := ch919122OK.all q h
    rwa [ch919122O] at e
  · have hq' : q - 102 < 101 := by omega
    have e := ch919122PK.all (q - 102) hq'
    rw [ch919122P, Nat.add_eq, Nat.add_sub_cancel' (by omega)] at e
    exact e

theorem rOrb : ∀ q < 2, chunkF RCR (cjG RCR) 5 36 32 q = true := by
  intro q hq
  have h := ch919122CK.all q hq
  rwa [ch919122C] at h

theorem oRefl : ∀ q < 102, reflChunk ROO 3 51840 RCR 36 512 q = true := by
  intro q hq
  have h := ch919122RK.all q hq
  rwa [ch919122R] at h

theorem oA6c : ∀ q < 102, a6cChunk ROO 3 51840 (RW 0) (RW 1) (ROO 2) 512 q = true := by
  intro q hq
  have h := ch919122WK.all q hq
  simp only [ch919122W, CFSG.KC.YamakiRepF.strictY_eq] at h
  exact h

theorem reflOrbitCheck_ok : reflOrbitCheck () = true :=
  reflOrbitCheck_of (L := 256) (m := 203) (L' := 512) (m' := 102) oMatAO oMatBO oMatRO oLtR rRoot
    (by norm_num) oHeadO oTabO rHdr rHead rOrb (by norm_num) oRefl

theorem a6Check_ok : a6Check () = true :=
  a6Check_of oMatA oMatB oMatR oMatC oMatD1 oMatD2 cMatRB oHdrLt cRootB oHead oTab oPosC oCent5
    oCent6 oCent7 wGen0 wGen1 wHead wTab cHdrB cHeadB cOrbB wCls

theorem a6CentCheck_ok : a6CentCheck () = true :=
  a6CentCheck_of (L := 256) (m := 203) (L' := 512) (m' := 102) oMatAO oMatBO oMatRO oLtR oMatC
    oMatD1 oMatD2 wGen0 wGen1 (by norm_num) oHeadO oTabO (by norm_num) oA6c

end CFSG.KD.OmegaSix

end

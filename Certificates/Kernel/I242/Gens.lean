module

public import Certificates.Kernel.I242.Checks
public import Certificates.Kernel.Sporadic.Fi22.F1Outer
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.O8ConstrSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelI242

open CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.Native CFSG.Monster.B.Co2.Native

@[expose] noncomputable def AK : Nat := CertificateChecks.KernelSpor.Fi22OutT.L 1

theorem fiveArr_eq {k : Nat} (hk : k < 8) : fi22FiveArr k = unpack 3510 12 (H.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound H.all k hk
  rw [← H.eq] at h
  exact h

theorem aArr_eq : fi22FiveAArr = unpack 3510 12 AK :=
  CertificateChecks.KernelSpor.Fi22F1O.arr3510_eq (by norm_num)

theorem idA_eq : idA 3510 = unpack 3510 12 pid := (idK_sound kId).symm

theorem cn_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) : cn (pc p q) = true :=
  canonK_pcomp hp hq

theorem compA_pc {p q : Nat} (hp : cn p = true) (hq : cn q = true) :
    compA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = unpack 3510 12 (pc p q) :=
  compA_unpack hp hq

theorem invCand_pinv {p : Nat} (hp : pm p = true) :
    invCand 3510 (unpack 3510 12 p) = unpack 3510 12 (pinv p) :=
  invCand_unpack hp

theorem cpK_iff {p : Nat} (h : cpK p = true) : cn p = true ∧ pm p = true ∧ cn (pinv p) = true := by
  unfold cpK at h
  simp only [bAnd_iff] at h
  exact h

theorem conjInv_eq {g y : Nat} (hg : cpK g = true) (hy : cn y = true) :
    conjInvA 3510 (unpack 3510 12 g) (unpack 3510 12 y) = unpack 3510 12 (cjI g y) := by
  obtain ⟨g1, g2, g3⟩ := cpK_iff hg
  unfold conjInvA
  rw [invCand_pinv g2, compA_pc hy g1, compA_pc g3 (cn_pc hy g1)]
  rfl

theorem comm_eq {g h : Nat} (hg : cpK g = true) (hh : cpK h = true) :
    commutatorA 3510 (unpack 3510 12 g) (unpack 3510 12 h) = unpack 3510 12 (cmK g h) := by
  obtain ⟨g1, g2, g3⟩ := cpK_iff hg
  obtain ⟨h1, h2, h3⟩ := cpK_iff hh
  unfold commutatorA
  rw [compA_pc g1 h1, invCand_pinv g2, invCand_pinv h2, compA_pc g3 h3,
    compA_pc (cn_pc g1 h1) (cn_pc g3 h3)]
  rfl

theorem parts_ok {i : Nat} (hi : i < 6) :
    cpK (hK H.F i) = true ∧ cpK (aK H.F AK i) = true ∧ cpK (bK H.F i) = true := by
  have h := allN_spec kParts i hi
  unfold partsK at h
  simp only [bAnd_iff] at h
  exact h

theorem hArr_eq {i : Nat} (hi : i < 6) : fi22FiveHArr i = unpack 3510 12 (hK H.F i) := by
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · have e0 : hK H.F 0 = pid := rfl
    rw [e0, ← idA_eq]
    unfold fi22FiveHArr
    rw [if_pos rfl]
  · have hb : Nat.beq i 0 = false := by
      cases e : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) (by omega)
    have e : hK H.F i = H.F (i + 2) := by
      unfold hK
      rw [hb]
    rw [e, ← fiveArr_eq (by omega)]
    unfold fi22FiveHArr
    rw [if_neg (by omega)]

theorem q2_cn : cn (H.F 1) = true :=
  ((bAnd_iff (cn (CertificateChecks.KernelSpor.Fi22OutT.L 1)) (cn (H.F 1))).1 kQA).2

theorem a_cn : cn AK = true :=
  ((bAnd_iff (cn (CertificateChecks.KernelSpor.Fi22OutT.L 1)) (cn (H.F 1))).1 kQA).1

theorem dgen0 (i : Nat) : (fi22FiveDGenArrs i)[0]! =
    commutatorA 3510 (fi22FiveCGenArrs i)[1]! (fi22FiveCGenArrs i)[2]! := rfl

theorem lit2_get1 (a b : Array Nat) : (#[a, b] : Array (Array Nat))[1]! = b := rfl

theorem dgen1 (i : Nat) : (fi22FiveDGenArrs i)[1]! = (fi22FiveCGenArrs i)[2]! := by
  unfold fi22FiveDGenArrs
  exact lit2_get1 _ _

theorem cA_eq {i : Nat} (hi : i < 6) :
    (fi22FiveCGenArrs i)[1]! = unpack 3510 12 (aK H.F AK i) := by
  change conjInvA 3510 (fi22FiveHArr i) fi22FiveAArr = _
  rw [hArr_eq hi, aArr_eq, conjInv_eq (parts_ok hi).1 a_cn]
  rfl

theorem cB_eq {i : Nat} (hi : i < 6) :
    (fi22FiveCGenArrs i)[2]! = unpack 3510 12 (bK H.F i) := by
  change conjInvA 3510 (fi22FiveHArr i) (fi22FiveArr 1) = _
  rw [hArr_eq hi, fiveArr_eq (by norm_num), conjInv_eq (parts_ok hi).1 q2_cn]
  rfl

theorem dGens_get {j : Nat} (hj : j < 12) : i242DGens[j]! = unpack 3510 12 (dK H.F AK j) := by
  have hs : j < i242DGens.size := by simp [i242DGens, hj]
  rw [getElem!_pos i242DGens j hs]
  simp only [i242DGens, Array.getElem_ofFn]
  have hi : j / 2 < 6 := by omega
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · have hb : Nat.beq (Nat.mod j 2) 0 = true := by
      rw [Nat.beq_eq]
      exact h
    have e : dK H.F AK j = cmK (aK H.F AK (j / 2)) (bK H.F (j / 2)) := by
      unfold dK
      rw [hb]
      rfl
    rw [h, e, dgen0, cA_eq hi, cB_eq hi, comm_eq (parts_ok hi).2.1 (parts_ok hi).2.2]
  · have hb : Nat.beq (Nat.mod j 2) 0 = false := by
      cases e : Nat.beq (Nat.mod j 2) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) (by change ¬ (j % 2 = 0); omega)
    have e : dK H.F AK j = bK H.F (j / 2) := by
      unfold dK
      rw [hb]
      rfl
    rw [h, e, dgen1]
    exact cB_eq hi

theorem dGens : i242DGens.size = 12 ∧ ∀ j < 12, i242DGens[j]! = unpack 3510 12 (dK H.F AK j) :=
  ⟨by simp [i242DGens], fun _ hj => dGens_get hj⟩

theorem permY : allN 17 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (Y.S j) (Y.SI j)) = true := by
  have h := Y.head
  unfold headK at h
  simp only [bAnd_iff] at h
  exact h.2.2.2.2.1

theorem yArrs : i242YArrs.size = 8 ∧ ∀ r < 8, i242YArrs[r]! = unpack 3510 12 (Y.S r) := by
  refine ⟨by simp [i242YArrs], fun r hr => ?_⟩
  have hs : r < i242YArrs.size := by simp [i242YArrs, hr]
  rw [getElem!_pos i242YArrs r hs]
  simp only [i242YArrs, Array.getElem_map, List.getElem_toArray, List.getElem_range]
  exact (wordEqK_sound dGens kD (allN_spec kY r hr)).1

end CertificateChecks.KernelI242

end

module

public import Certificates.Kernel.U38R.Checks
public import CFSG.Certificates.Kernel.U38RSound
public import Certificates.Kernel.SchreierFam.C188001F
public import Certificates.Kernel.U38.Facts
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.PGrpSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38R

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.K426K CFSG.KC.B3S3K
  CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim CFSG.RankThree.PartTwo.Sec4.Item434U38
open CFSG.Monster.B.Co2 (allLt_iff compA_get)

theorem hN : UR.N = 729 := Nat.eq_of_beq_eq_true nums.1

theorem hng : UR.ng = 3 := Nat.eq_of_beq_eq_true nums.2

theorem arrRH {k : ℕ} (hk : k < 12) :
    hexTable 3 513 (513 * k) dataHex = unpack 513 10 (RH.F k) := by
  rw [RH.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound RH.all k hk

theorem pRH {k : ℕ} (hk : k < 12) : permB 513 10 (RH.F k) = true := Orb.allN_iff.1 permRH k hk

theorem rGens_size : (rGens ()).size = 3 := by
  rw [rGens, Array.size_ofFn]

theorem rGens_get {j : ℕ} (hj : j < 3) : (rGens ())[j]! = unpack 513 10 (RH.F j) := by
  rw [rGens, KernelU38.getOfFn' (f := fun j => hexTable 3 513 (513 * j) dataHex) hj]
  exact arrRH (by omega)

theorem hList_size : (hList ()).size = 9 := by
  rw [hList, Array.size_ofFn]

theorem hList_get {k : ℕ} (hk : k < 9) : (hList ())[k]! = unpack 513 10 (RH.F (3 + k)) := by
  rw [hList, KernelU38.getOfFn' (f := fun j => hexTable 3 513 (513 * (3 + j)) dataHex) hk]
  exact arrRH (by omega)

theorem pG : ∀ k < UR.ng,
    permOK 513 10 (mask 10) (513 * 10) (UR.G k) (pinvS 513 10 (mask 10) (UR.G k)) = true := by
  rw [hng]
  intro k hk
  rw [Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gensR k hk)]
  exact pRH (by omega)

theorem pT {i : ℕ} (hi : i < 729) : permB 513 10 (UR.T i) = true :=
  permB_of_pp (PP_pts UR.ok pG i (by rw [hN]; exact hi))

theorem enumR : enumOK 513 (rGens ()) ps (rCert ()) = true ∧ (rCert ()).pts.size = 729 ∧
    ∀ i < 729, (rCert ()).pts[i]! = unpack 513 10 (UR.T i) := by
  have hb : BindA 513 10 (rGens ()) UR.ng UR.G := by
    rw [hng]
    refine ⟨rGens_size, fun j hj => ?_⟩
    rw [rGens_get hj, Nat.eq_of_beq_eq_true (Orb.allN_iff.1 gensR j hj)]
  have h := enum_of (ps := ps) (fuel := 800) hb pG UR.ok CFSG.KC.U38R.hps UR.keys
    (by rw [hN]; omega)
  rw [hN] at h
  exact h

theorem E_get {i : ℕ} (hi : i < 729) : (rCert ()).pts[i]! = unpack 513 10 (UR.T i) :=
  enumR.2.2 i hi

theorem hK : ∀ m < (rCert ()).pts.size,
    keyIdx 513 10 KR (keyA 513 ps (rCert ()).pts[m]!) = m := by
  intro m hm
  rw [enumR.2.1] at hm
  rw [E_get hm, keyA_unpackK CFSG.KC.U38R.hps, CFSG.KC.U38R.ps_eq]
  exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 kIdx m hm)

theorem keyProd_R {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    keyProd (rCert ()).pts i j = keyCK 513 10 [0, 1] (UR.T i) (UR.T j) := by
  rw [CFSG.KC.U38R.keyProd_eq, E_get hi, E_get hj, comp_unpack' kW (pT hi) (pT hj),
    keyA_unpackK CFSG.KC.U38R.hps, CFSG.KC.U38R.ps_eq]
  exact keyK_pcomp (n := 513) (w := 10) (by norm_num) (UR.T i) (UR.T j) (ps := [0, 1])
    (by decide)

theorem mulI_R {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    mulI (mulTab (rCert ()).pts) i j = mulK i j := by
  have hs := enumR.2.1
  rw [CFSG.KC.U38R.mulI_mulTab enumR.1 hK (by rw [hs]; exact hi) (by rw [hs]; exact hj),
    keyProd_R hi hj]
  rfl

theorem tabOK_R : tabOK (rCert ()).pts (mulTab (rCert ()).pts) = true :=
  CFSG.KC.U38R.tabOK_mulTab enumR.1 hK

theorem genOK_R : genOK (rGens ()) = true := by
  unfold genOK
  dsimp only
  rw [allLt_iff]
  intro k hk
  rw [rGens_size] at hk
  rw [rGens_get hk, CFSG.KC.BfsPin.validA_unpack (pRH (by omega)), Bool.true_and]
  exact siftA_of_siftOK KernelSchreierFam.U38B.binds1 KernelSchreierFam.U38B.perm1
    KernelSchreierFam.U38C1.hl (Orb.allN_iff.1 sift1R k hk)

theorem hsOK_R : hsOK (rawLevels 513 strong3 base3) (hList ()) = true := by
  unfold hsOK
  rw [allLt_iff]
  intro k hk
  rw [hList_size] at hk
  rw [hList_get hk, CFSG.KC.BfsPin.validA_unpack (pRH (by omega)), Bool.true_and]
  exact siftA_of_siftOK KernelU38.binds KernelU38.permX KernelU38.UX.hl
    (Orb.allN_iff.1 siftHR k hk)

theorem siftA_T {i : ℕ} (hi : i < 729) :
    siftA 513 (rawLevels 513 strong3 base3) base3 0 (unpack 513 10 (UR.T i)) = siftXK (UR.T i) := by
  have hc := bfsK_canon UR.ok i (by rw [hN]; exact hi)
  unfold CFSG.KS.Prim.canonK at hc
  simp only [bAnd_iff] at hc
  exact siftK_eq KernelU38.binds KernelU38.permX KernelU38.UX.hl rfl
    (Nat.eq_of_beq_eq_true hc.2.1) hc.2.2

theorem flag_eq {i : ℕ} (hi : i < 729) : siftXK (UR.T i) = Nat.beq (ixBit i) 1 := by
  have h := Orb.allN_iff.1 flagsR i hi
  cases hs : siftXK (UR.T i)
  · rw [hs] at h
    change Nat.beq (ixBit i) 0 = true at h
    rw [Nat.eq_of_beq_eq_true h]
    rfl
  · rw [hs] at h
    exact h.symm

theorem inX_get {i : ℕ} (hi : i < 729) :
    (inXArr (rawLevels 513 strong3 base3) (rCert ()).pts)[i]! = Nat.beq (ixBit i) 1 := by
  have hs : i < (rCert ()).pts.size := by rw [enumR.2.1]; exact hi
  unfold inXArr
  rw [getElem!_pos _ i (by simpa using hs), Array.getElem_map, ← getElem!_pos (rCert ()).pts i hs,
    E_get hi, siftA_T hi, flag_eq hi]

theorem flagged_R :
    (flagged (inXArr (rawLevels 513 strong3 base3) (rCert ()).pts) (rCert ()).pts.size).length =
      81 := by
  rw [enumR.2.1]
  unfold flagged
  rw [List.filter_congr (fun i hi => inX_get (List.mem_range.1 hi)), ← sumN_count]
  exact Nat.eq_of_beq_eq_true cntR

end CertificateChecks.KernelU38R

end

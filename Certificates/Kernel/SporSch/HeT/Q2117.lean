module

public import Certificates.Kernel.SporSch.HeT.Q2117K
public import Certificates.Kernel.SporSch.HeT.PtGlue
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HeAutKSound
public import CFSG.Certificates.Kernel.HeFixKSound
public import CFSG.Certificates.Kernel.PermToolSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeQ17

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.ChainCls CFSG.Certificates CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148 CertificateChecks.KernelSporSch.HePt
open CFSG.KC.BfsPin CFSG.Monster.B.Mathieu

theorem kOs : Nat.beq (ordK QC.LR 4) 15120 = true ∧ Nat.beq (ordK QD.LR 4) 7560 = true ∧
    Nat.beq (ordK QE.LR 4) 7560 = true ∧ Nat.beq (ordK QY.LR 4) 2520 = true := by
  simpa only [bAnd_iff] using kO

theorem kZs : siftK 98 7 (mask 7) (98 * 7) (pidn 98 7) QD.LR QD.TRI QD.BP 4 0 Z = true ∧
    allN 3 (fun j => Nat.beq (pc Z (QD.S j)) (pc (QD.S j) Z)) = true ∧
    neIdK 98 7 (mask 7) (98 * 7) (pidn 98 7) Z = true ∧
    Nat.beq (pc Z (pc Z Z)) (pidn 98 7) = true ∧ idK 98 7 (mask 7) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (pidn 98 7) = true ∧
    Nat.beq (CFSG.KC.HeFixK.fixK 98 7 Z) 35 = true ∧
    allN 35 (fun k => Nat.beq (pg 7 (mask 7) Z (nget FZ k)) (nget FZ k)) = true := by
  simpa only [bAnd_iff] using kZ

theorem kCs : Nat.ble (ordK QD.LR 4) (Nat.mul QDC.CS.length 2048) = true ∧
    Nat.beq QDC.CS.sum 3 = true := by
  simpa only [bAnd_iff] using kC

theorem atQC {j : Nat} (hj : j < 2) :
    BindAt 98 7 (QC.S j) (QC.SI j) ([heSigma1, heSigma2].getD j #[]) := by
  have h := bindsK_spec bQC j (by simpa using hj)
  rwa [Nat.zero_add] at h

theorem atQY {j : Nat} (hj : j < 3) :
    BindAt 35 6 (QY.S j) (QY.SI j) (heUpsilon.getD j #[]) := by
  have h := bindsK_spec bQY j (by simpa [heUpsilon] using hj)
  rwa [Nat.zero_add] at h

theorem atZ : BindAt 98 7 Z (ZP 1) heZ := bindsK_spec bZ 0 (by simp)

theorem Z_eq : heZ = unpack 98 7 Z := (bind_facts atZ).1

theorem cZ : canonK 98 7 (mask 7) (98 * 7) Z = true := atZ.2.2.2.1

theorem sig_eq {j : Nat} (hj : j < 2) : heSigmaArrs[j]! = unpack 98 7 (QC.S j) := by
  have h := (bind_facts (atQC hj)).1
  interval_cases j
  · simpa [heSigmaArrs] using h
  · simpa [heSigmaArrs] using h

theorem tau_parts {j : Nat} (hj : j < 3) :
    wordEqK 98 7 (mask 7) (pidn 98 7) QC.S QC.SI 2 (heDerivedV.getD j []) (QD.S j) = true ∧
    invEqK 98 7 (mask 7) (98 * 7) (QD.S j) (QD.SI j) = true ∧
    invEqK 98 7 (mask 7) (98 * 7) (QD.SI j) (QD.S j) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (QD.S j) = true ∧
    canonK 98 7 (mask 7) (98 * 7) (QD.SI j) = true := by
  simpa only [tauK, bAnd_iff] using allN_spec kTau j hj

theorem tau_eq {j : Nat} (hj : j < 3) : heTauArr j = unpack 98 7 (QD.S j) :=
  (wordEqK_sound ⟨rfl, fun _ hl => sig_eq hl⟩ kP (tau_parts hj).1).1

theorem tau_inv {j : Nat} (hj : j < 3) : invCand 98 (heTauArr j) = unpack 98 7 (QD.SI j) := by
  rw [tau_eq hj]
  exact (invEqK_sound (tau_parts hj).2.1).1

theorem eps_parts {i : Nat} (hi : i < 2) :
    Nat.beq (pc (QD.S i) (pc (QD.S 2) (pc (QD.SI i) (QD.SI 2)))) (QE.S i) = true ∧
    invEqK 98 7 (mask 7) (98 * 7) (QE.S i) (QE.SI i) = true ∧
    invEqK 98 7 (mask 7) (98 * 7) (QE.SI i) (QE.S i) = true := by
  simpa only [epsK, bAnd_iff] using allN_spec kEps i hi

theorem eps_eq {i : Nat} (hi : i < 2) : heEpsArr i = unpack 98 7 (QE.S i) := by
  obtain ⟨-, -, -, ci, cii⟩ := tau_parts (j := i) (by omega)
  obtain ⟨-, -, -, c2, ci2⟩ := tau_parts (j := 2) (by norm_num)
  rw [heEpsArr, tau_inv (by omega), tau_inv (by norm_num), tau_eq (by omega), tau_eq (by norm_num),
    compA_unpack cii ci2, compA_unpack c2 (canonK_pcomp cii ci2),
    compA_unpack ci (canonK_pcomp c2 (canonK_pcomp cii ci2))]
  exact congrArg (unpack 98 7) (Nat.eq_of_beq_eq_true (eps_parts hi).1)

theorem tau_img {j : Nat} (hj : j < 3) :
    imageList (permOrId 98 (heTauArr j)) = (unpack 98 7 (QD.S j)).toList :=
  imageList_of_rep (unpack_size' _ _ _)
    (unpack_facts (tau_eq hj) (tau_parts hj).2.1 (tau_parts hj).2.2.1).2.1

theorem eps_img {i : Nat} (hi : i < 2) :
    imageList (permOrId 98 (heEpsArr i)) = (unpack 98 7 (QE.S i)).toList :=
  imageList_of_rep (unpack_size' _ _ _)
    (unpack_facts (eps_eq hi) (eps_parts hi).2.1 (eps_parts hi).2.2).2.1

theorem chainQC : ChainK 98 7 [permOrId 98 heSigma1, permOrId 98 heSigma2] heQCWords
    (#v[0, 1, 6, 3] : Vector (Fin 98) 4) QC.S QC.SI QC.LR QC.TR QC.TRI 7 QC.BP 7 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QC.head, QC.hl,
    by norm_num, QC.hs⟩
  have hj' : j < 2 := by simpa using hj
  interval_cases j
  · exact imageList_bind (atQC (j := 0) (by norm_num))
  · exact imageList_bind (atQC (j := 1) (by norm_num))

theorem chainQD : ChainK 98 7 heTauGens heQDWords (#v[0, 1, 3, 6] : Vector (Fin 98) 4) QD.S QD.SI
    QD.LR QD.TR QD.TRI 7 QD.BP 7 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QD.head, QD.hl,
    by norm_num, QD.hs⟩
  have hj' : j < 3 := by simpa [heTauGens] using hj
  interval_cases j
  · exact tau_img (j := 0) (by norm_num)
  · exact tau_img (j := 1) (by norm_num)
  · exact tau_img (j := 2) (by norm_num)

theorem chainQE : ChainK 98 7 [permOrId 98 (heEpsArr 0), permOrId 98 (heEpsArr 1)] heQEWords
    (#v[0, 1, 3, 6] : Vector (Fin 98) 4) QE.S QE.SI QE.LR QE.TR QE.TRI 7 QE.BP 7 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QE.head, QE.hl,
    by norm_num, QE.hs⟩
  have hj' : j < 2 := by simpa using hj
  interval_cases j
  · exact eps_img (i := 0) (by norm_num)
  · exact eps_img (i := 1) (by norm_num)

theorem chainQY : ChainK 35 6 heUpsGens heQYWords (#v[0, 1, 3, 2] : Vector (Fin 35) 4) QY.S
    QY.SI QY.LR QY.TR QY.TRI 8 QY.BP 3 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QY.head, QY.hl,
    by norm_num, QY.hs⟩
  have hj' : j < heUpsilon.length := by simpa [heUpsGens] using hj
  rw [heUpsGens, getD_map_lt _ #[] _ hj']
  exact imageList_bind (atQY (by simpa [heUpsilon] using hj'))

theorem eqA_of {n w p q : Nat} (h : Nat.beq p q = true) : eqA n (unpack n w p) (unpack n w q) = true :=
  eqK_sound h

theorem small : heQC.check = true ∧ heQC.orderCertificate = 15120 ∧ heQD.check = true ∧
    heQD.orderCertificate = 7560 ∧ heQE.check = true ∧ heQE.orderCertificate = 7560 ∧
    permChk 98 (heEpsArr 0) = true ∧ permChk 98 (heEpsArr 1) = true ∧ permChk 98 heZ = true ∧
    heQD.sift (permOrId 98 heZ) 0 = true ∧
    (∀ j < 3, eqA 98 (compA 98 heZ (heTauArr j)) (compA 98 (heTauArr j) heZ) = true) ∧
    eqA 98 heZ (idA 98) = false ∧ eqA 98 (compA 98 heZ (compA 98 heZ heZ)) (idA 98) = true ∧
    (allTables heQD).countP (commAll 98 (heTauGens.map toTable)) = 3 ∧
    fixListOK 98 35 heZ heFixZ = true ∧
    (∀ j < 3, permChk 35 (heUpsilon.getD j #[]) = true ∧
      agreeOK 35 (heTauArr j) heFixZ (heUpsilon.getD j #[]) = true) ∧
    heQY.check = true ∧ heQY.orderCertificate = 2520 := by
  obtain ⟨o1, o2, o3, o4⟩ := kOs
  obtain ⟨zs, zc, zne, z3, zid, -, zcnt, zfix⟩ := kZs
  obtain ⟨cL, cS⟩ := kCs
  obtain ⟨fe, fl, flt, finc⟩ := kF
  obtain ⟨qc1, qc2⟩ := chainK_check (by decide) (by decide) chainQC
  obtain ⟨qd1, qd2⟩ := chainK_check (by decide) (by decide) chainQD
  obtain ⟨qe1, qe2⟩ := chainK_check (by decide) (by decide) chainQE
  obtain ⟨qy1, qy2⟩ := chainK_check (by decide) (by decide) chainQY
  have hN : ordK QD.LR 4 = 7560 := Nat.eq_of_beq_eq_true o2
  have hG : ∀ i < heTauGens.length, imageList (heTauGens.getD i 1) = (unpack 98 7 (QD.S i)).toList ∧
      canonK 98 7 (mask 7) (98 * 7) (QD.S i) = true := by
    intro i hi
    have hi' : i < 3 := by simpa [heTauGens] using hi
    refine ⟨?_, (tau_parts hi').2.2.2.1⟩
    interval_cases i
    · exact tau_img (j := 0) (by norm_num)
    · exact tau_img (j := 1) (by norm_num)
    · exact tau_img (j := 2) (by norm_num)
  have hc : ∀ s < QDC.CS.length, commCntK 98 7 (mask 7) (98 * 7) (pidn 98 7) QD.LR QD.TR 4 QD.S
      heTauGens.length (ordK QD.LR 4) (s * 2048) 2048 = QDC.CS.getD s 0 := by
    intro s hs
    rw [hN]
    have hl : QDC.CS.length = 4 := rfl
    exact Nat.eq_of_beq_eq_true (QDC.E.all s (lt_of_lt_of_eq hs hl))
  have hcnt := chainK_commAllCount (by decide) (by decide) chainQD hG
    (Nat.le_of_ble_eq_true cL) hc
  refine ⟨qc1, qc2.trans (Nat.eq_of_beq_eq_true o1), qd1, qd2.trans hN, qe1,
    qe2.trans (Nat.eq_of_beq_eq_true o3), perm_of (eps_eq (i := 0) (by norm_num))
      (eps_parts (i := 0) (by norm_num)).2.1 (eps_parts (i := 0) (by norm_num)).2.2,
    perm_of (eps_eq (i := 1) (by norm_num)) (eps_parts (i := 1) (by norm_num)).2.1
      (eps_parts (i := 1) (by norm_num)).2.2, (bind_facts atZ).2.1,
    chainK_sift (by decide) (by decide) chainQD (imageList_bind atZ) cZ zs, fun j hj => ?_, ?_, ?_,
    hcnt.trans (Nat.eq_of_beq_eq_true cS),
    fixList_ok fe fl Z_eq flt finc zfix (Nat.eq_of_beq_eq_true zcnt), fun j hj => ⟨?_, ?_⟩, qy1,
    qy2.trans (Nat.eq_of_beq_eq_true o4)⟩
  · have ct := (tau_parts hj).2.2.2.1
    rw [Z_eq, tau_eq hj, compA_unpack cZ ct, compA_unpack ct cZ]
    exact eqA_of (allN_spec zc j hj)
  · rw [Z_eq]
    exact neIdK_sound zne
  · rw [Z_eq, compA_unpack cZ cZ, compA_unpack cZ (canonK_pcomp cZ cZ), ← idK_sound zid]
    exact eqA_of z3
  · exact (bind_facts (atQY hj)).2.1
  · exact agree_ok fe fl (tau_eq hj) (bind_facts (atQY hj)).1 (atQY hj).2.2.2.1 flt
      (allN_spec kU j hj)

end CertificateChecks.KernelSporSch.HeQ17

end

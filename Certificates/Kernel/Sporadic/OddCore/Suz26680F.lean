module

public import Certificates.Kernel.Sporadic.OddCore.Suz26680S0
public import Certificates.Kernel.Sporadic.OddCore.Suz26680S1
public import Certificates.Kernel.Sporadic.OddCore.Suz26990F
public import Certificates.Kernel.Sporadic.OddCore.SuzCTF0
public import Certificates.Kernel.Sporadic.OddCore.Suz2303F
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSSuzCheck
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.HeAutKSound
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.S26680.kSlAll CertificateChecks.KernelSpor.S26680.kSl 16

namespace CertificateChecks.KernelSpor.S26680

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34KSnd
open CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.Suz2306
open CertificateChecks.KernelSpor.S26990
open CFSG.EvenSporadicStandard.Solomon78 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.PSL3Four.Native CFSG.Certificates.Native
open CFSG.KLie.CT (andB orB notB)

theorem letters : lettersK 3 suzWordL = true ∧ lettersK 2 suzWordZ = true ∧
    lettersK 4 suzWordG0 = true ∧ lettersK 4 suzWordG1 = true := by
  have h := kLet
  simp only [andB_iff] at h
  exact h

theorem parts :
    (Cn PL ∧ Cn (pinv PL) ∧ permOK 1782 11 (mask 11) (1782 * 11) PL (pinv PL) = true) ∧
    (Cn PAl ∧ Cn (pinv PAl) ∧ permOK 1782 11 (mask 11) (1782 * 11) PAl (pinv PAl) = true) ∧
    (Cn PBl ∧ Cn (pinv PBl) ∧ permOK 1782 11 (mask 11) (1782 * 11) PBl (pinv PBl) = true) ∧
    Cn PZ ∧ Cn B0 ∧ Cn B1 := by
  have h := kInv
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h6⟩ := andB_iff.1 h
  exact ⟨ok_spec h1, ok_spec h2, ok_spec h3, h4, h5, h6⟩

theorem cA : Cn PA := inv_parts.1.1
theorem cB : Cn PB := inv_parts.2.1
theorem cL : Cn PL := parts.1.1
theorem cZ : Cn PZ := parts.2.2.2.1
theorem cT : Cn (SuzTP 0) := all_parts.2.2.2.2.2.2.2.2.2

theorem pl_eq : suzArrL = unpack 1782 11 PL := by
  unfold suzArrL PL
  exact w3_eq letters.1

theorem pz_eq : suzArrZ = unpack 1782 11 PZ := by
  unfold suzArrZ PZ WK
  rw [abi_eq]
  exact word_of ab_bind ab_p letters.2.1

theorem invL : invCand 1782 (unpack 1782 11 PL) = unpack 1782 11 (pinv PL) :=
  (inv_u (a := unpack 1782 11 PL) rfl parts.1.2.2).1

theorem pal_eq : suzArrAl = unpack 1782 11 PAl := by
  unfold suzArrAl suzConj PAl
  rw [pl_eq, pa_eq, invL, S26990.compA_u cL cA, S26990.compA_u (cpc cL cA) parts.1.2.1]

theorem pbl_eq : suzArrBl = unpack 1782 11 PBl := by
  unfold suzArrBl suzConj PBl
  rw [pl_eq, pb_eq, invL, S26990.compA_u cL cB, S26990.compA_u (cpc cL cB) parts.1.2.1]

theorem four_bind : suzArr4.size = 4 ∧
    ∀ j < 4, suzArr4[j]! = unpack 1782 11 (sel4 PA PB PAl PBl j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => exact pa_eq
  | 1, _ => exact pb_eq
  | 2, _ => exact pal_eq
  | 3, _ => exact pbl_eq

theorem four_p : ∀ j < 4, permOK 1782 11 (mask 11) (1782 * 11) (sel4 PA PB PAl PBl j)
    (sel4 (pinv PA) (pinv PB) (pinv PAl) (pinv PBl) j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact inv_parts.1.2.2
  | 1, _ => exact inv_parts.2.2.2
  | 2, _ => exact parts.2.1.2.2
  | 3, _ => exact parts.2.2.1.2.2

theorem four_i : suzArr4i = rawInvs 1782 suzArr4 := by
  unfold suzArr4i suzArrAi suzArrBi suzArrAli suzArrBli
  simp [rawInvs, suzArr4]

theorem w4_eq {wd : List Int} (hl : lettersK 4 wd = true) :
    wordA 1782 suzArr4 suzArr4i wd = unpack 1782 11 (W4 wd) := by
  unfold W4
  rw [four_i]
  exact word_of four_bind four_p hl

theorem lettersC : suzLettersOK = true := by
  decide +kernel

theorem invC : suzInvOK = true := by
  have iA : isInvA 1782 suzArrA suzArrAi = true := by
    unfold suzArrAi
    exact (inv_u pa_eq inv_parts.1.2.2).2
  have iB : isInvA 1782 suzArrB suzArrBi = true := by
    unfold suzArrBi
    exact (inv_u pb_eq inv_parts.2.2.2).2
  have iL : isInvA 1782 suzArrL suzArrLi = true := by
    unfold suzArrLi
    exact (inv_u pl_eq parts.1.2.2).2
  have iAl : isInvA 1782 suzArrAl suzArrAli = true := by
    unfold suzArrAli
    exact (inv_u pal_eq parts.2.1.2.2).2
  have iBl : isInvA 1782 suzArrBl suzArrBli = true := by
    unfold suzArrBli
    exact (inv_u pbl_eq parts.2.2.1.2.2).2
  unfold suzInvOK
  rw [iA, iB, iL, iAl, iBl]
  rfl

theorem rel_parts : Nat.beq (ppow 1782 11 (mask 11) e PA 3) e = true ∧
    Nat.beq (ppow 1782 11 (mask 11) e PB 3) e = true ∧ SuzTP 0 = B0 ∧
    Nat.beq (pc PA (SuzTP 0)) (pc (SuzTP 0) PA) = true ∧
    Nat.beq (pc PB (SuzTP 0)) (pc (SuzTP 0) PB) = true ∧
    Nat.beq (pc (pc PL (SuzTP 0)) (pinv PL)) (pc (SuzTP 0) PZ) = true ∧
    W4 suzWordG0 = B0 ∧ W4 suzWordG1 = B1 ∧ Nat.beq (pc PZ PZ) e = true := by
  have h := kRel
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h⟩ := andB_iff.1 h
  obtain ⟨h8, h9⟩ := andB_iff.1 h
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, h4, h5, h6, Nat.eq_of_beq_eq_true h7,
    Nat.eq_of_beq_eq_true h8, h9⟩

theorem pow3 {P : Nat} (hP : Cn P) (h : Nat.beq (ppow 1782 11 (mask 11) e P 3) e = true) :
    eqA 1782 (powA 1782 (unpack 1782 11 P) 3) (idA 1782) = true := by
  rw [powA_unpack hP 3, hidA, S26990.eqA_u (canon_ppow hP 3) cE]
  exact h

theorem commT {P : Nat} (hP : Cn P) (h : Nat.beq (pc P (SuzTP 0)) (pc (SuzTP 0) P) = true) :
    eqA 1782 (compA 1782 (unpack 1782 11 P) (tArr 0)) (compA 1782 (tArr 0) (unpack 1782 11 P)) =
      true := by
  rw [t0_eq, S26990.compA_u hP cT, S26990.compA_u cT hP, S26990.eqA_u (cpc hP cT) (cpc cT hP)]
  exact h

theorem relC : suzRelOK = true := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := rel_parts
  have cB0 := parts.2.2.2.2.1
  have cB1 := parts.2.2.2.2.2
  have e1 : eqA 1782 (powA 1782 suzArrA 3) (idA 1782) = true := by
    rw [pa_eq]
    exact pow3 cA r1
  have e2 : eqA 1782 (powA 1782 suzArrB 3) (idA 1782) = true := by
    rw [pb_eq]
    exact pow3 cB r2
  have e3 : eqA 1782 (tArr 0) b0Arr = true := by
    rw [t0_eq, b0Arr_eq, r3, S26990.eqA_u cB0 cB0]
    exact Nat.beq_refl _
  have e4 : eqA 1782 (compA 1782 suzArrA (tArr 0)) (compA 1782 (tArr 0) suzArrA) = true := by
    rw [pa_eq]
    exact commT cA r4
  have e5 : eqA 1782 (compA 1782 suzArrB (tArr 0)) (compA 1782 (tArr 0) suzArrB) = true := by
    rw [pb_eq]
    exact commT cB r5
  have e6 : eqA 1782 (suzConj suzArrL (tArr 0)) (compA 1782 (tArr 0) suzArrZ) = true := by
    unfold suzConj
    rw [pl_eq, t0_eq, pz_eq, invL, S26990.compA_u cL cT, S26990.compA_u (cpc cL cT) parts.1.2.1,
      S26990.compA_u cT cZ, S26990.eqA_u (cpc (cpc cL cT) parts.1.2.1) (cpc cT cZ)]
    exact r6
  have e7 : eqA 1782 (wordA 1782 suzArr4 suzArr4i suzWordG0) b0Arr = true := by
    rw [w4_eq letters.2.2.1, r7, b0Arr_eq, S26990.eqA_u cB0 cB0]
    exact Nat.beq_refl _
  have e8 : eqA 1782 (wordA 1782 suzArr4 suzArr4i suzWordG1) b1Arr = true := by
    rw [w4_eq letters.2.2.2, r8, b1Arr_eq, S26990.eqA_u cB1 cB1]
    exact Nat.beq_refl _
  have e9 : eqA 1782 (compA 1782 suzArrZ suzArrZ) (idA 1782) = true := by
    rw [pz_eq, S26990.compA_u cZ cZ, hidA, S26990.eqA_u (cpc cZ cZ) cE]
    exact r9
  unfold suzRelOK
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  rfl

theorem fix_z : fixedCountN 1782 suzArrZ = fixN PZ := by
  unfold fixedCountN CFSG.Sporadic.SuzOddCore.fixedList fixN
  rw [pz_eq]
  refine congrArg List.length (List.filter_congr fun p hp => ?_)
  rw [CFSG.KC.BfsPin.unpack_get' (List.mem_range.1 hp)]
  cases h : Nat.beq (pg 11 (mask 11) PZ p) p
  · exact beq_false_of_ne (Nat.ne_of_beq_eq_false h)
  · rw [Nat.eq_of_beq_eq_true h]
    exact beq_self_eq_true _

theorem fix_t : fixedCountN 1782 (tArr 0) = 42 := by
  have h : fixedCountN 1782 (tArr 0) = (fixList 0).length := rfl
  rw [h, SuzD.fixList_eq, SuzD.fixL0_length]

theorem fixC : suzFixOK = true := by
  unfold suzFixOK
  rw [fix_z, fix_t, Nat.eq_of_beq_eq_true kFix]
  rfl

theorem hL : ∀ x ∈ SuzD.fixL0, x < 1782 := fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1

theorem res_eq {a : Array Nat} {P : Nat} (ha : a = unpack 1782 11 P) (hc : Cn P) :
    restrictArr (fixList 0) a = unpack 42 6 (res P) := by
  unfold res
  rw [ha, SuzD.fixList_eq,
    CFSG.KC.PermTool.restrictArr_unpack (w' := 6) hc hL (by rw [SuzD.fixL0_length]; decide),
    SuzD.fixL0_length]

theorem res_parts : canonK 42 6 (mask 6) (42 * 6) (res PA) = true ∧
    canonK 42 6 (mask 6) (42 * 6) (res PB) = true ∧
    canonK 42 6 (mask 6) (42 * 6) (res PZ) = true ∧ Nat.beq (res PZ) (pidn 42 6) = false := by
  have h := kRes
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h4⟩ := andB_iff.1 h
  refine ⟨h1, h2, h3, ?_⟩
  cases hb : Nat.beq (res PZ) (pidn 42 6)
  · rfl
  · rw [hb] at h4
    exact absurd h4 (by decide)

theorem tabA : suzTabA = unpack 42 6 (res PA) := by
  unfold suzTabA
  exact res_eq pa_eq cA

theorem tabB : suzTabB = unpack 42 6 (res PB) := by
  unfold suzTabB
  exact res_eq pb_eq cB

theorem tabZ : suzTabZ = unpack 42 6 (res PZ) := by
  unfold suzTabZ
  exact res_eq pz_eq cZ

theorem zC : suzZCheck = true := by
  unfold suzZCheck
  rw [tabZ, idTab_unpack' CFSG.KC.L34Scan.hsz42, bne,
    CFSG.KC.L34KSnd.beq_unpack res_parts.2.2.1 (canon_pidn CFSG.KC.L34Scan.hsz42), res_parts.2.2.2]
  rfl

theorem hd_parts : PK.cnt = 20160 ∧ PK.k = 2 ∧ penumHdK (pidn 42 6) PK.cnt 20160 PK.T PK.PL = true ∧
    PK.G 0 = res PA ∧ PK.G 1 = res PB := by
  have h := kHd
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h5⟩ := andB_iff.1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5⟩

theorem gensK : GensOK 42 6 2 PK.G suzTabs := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => rw [hd_parts.2.2.2.1]; exact ⟨tabA, res_parts.1⟩
  | 1, _ => rw [hd_parts.2.2.2.2]; exact ⟨tabB, res_parts.2.1⟩

theorem ptK : ∀ i < PK.cnt, penumPtK 42 6 (mask 6) (42 * 6) false PK.G PK.GI 2 PK.cnt PK.T
    PK.PL PK.POS PK.SRT PK.SRI i = true := by
  intro i hi
  have hi' : i < 20160 := hd_parts.1 ▸ hi
  have hs : i / 1260 < 16 := by omega
  exact penumSl_spec (kSlAll (i / 1260) hs) i (by change i / 1260 * 1260 ≤ i; omega)
    (by change i < i / 1260 * 1260 + 1260; omega) hi

theorem encK : enumBFS 42 suzTabs 20160 = penumRec 42 6 PK.cnt PK.T PK.PL ∧
    enumOK 42 suzTabs (penumRec 42 6 PK.cnt PK.T PK.PL) = true :=
  penumK_left_sound CFSG.KC.L34Scan.hsz42 gensK hd_parts.2.2.1 ptK

theorem genC : suzGenCheck = true := by
  unfold suzGenCheck enumOf
  rw [encK.1, encK.2, penumRec_eq, Array.size_ofFn, hd_parts.1]
  rfl

theorem clsC : suzClassCheck = true := by
  unfold suzClassCheck
  rw [List.all_eq_true]
  intro l hl
  have hl' := List.mem_range.1 hl
  have h := allN_spec kCls l hl'
  have c := SuzCT.root_canon hl'
  rw [SuzCT.rep_eq hl', comp_unpack' c c, idTab_unpack' CFSG.KC.L34Scan.hsz42, bne,
    CFSG.KC.L34KSnd.beq_unpack (CFSG.KC.BfsPin.canonK_pcomp c c) (canon_pidn CFSG.KC.L34Scan.hsz42)]
  simp only [orB_iff, notB_iff] at h
  rcases h with h | h | h
  · rw [Nat.eq_of_beq_eq_true h]
    rfl
  · rw [Nat.eq_of_beq_eq_true h]
    rfl
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact Or.inr (by simpa using h)

theorem check26680 : suzRowCheck = true := by
  unfold suzRowCheck
  rw [lettersC, invC, relC, fixC, genC, clsC, zC]
  rfl

end CertificateChecks.KernelSpor.S26680

end

module

public import Certificates.Kernel.Sporadic.OddCore.Suz26990E0
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E1
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E2
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E3
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E4
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E5
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E6
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E7
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E8
public import Certificates.Kernel.Sporadic.OddCore.Suz26990E9
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.PEnumSound
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Certificates.Kernel.PermToolSound
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.S26990.kSlAll CertificateChecks.KernelSpor.S26990.kSl 630

namespace CertificateChecks.KernelSpor.S26990

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.L34KSnd
open CertificateChecks.KernelSpor.OddCore CertificateChecks.KernelSpor.Suz2306
open CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CFSG.Certificates.Native
open CFSG.KLie.CT (andB orB notB)

attribute [local irreducible] idTab idA

abbrev Cn (p : Nat) : Prop := canonK 1782 11 (mask 11) (1782 * 11) p = true

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem hsz : szOK 1782 11 = true := by decide

theorem cE : Cn e := canon_pidn hsz

theorem hidA : idA 1782 = unpack 1782 11 e := by
  rw [← CFSG.KC.PermTool.idTab_eq]
  exact idTab_unpack' hsz

theorem cpc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem compA_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compA 1782 (unpack 1782 11 p) (unpack 1782 11 q) = unpack 1782 11 (pc p q) := by
  rw [← CFSG.KC.PermTool.comp_eq]
  exact comp_unpack' hp hq

theorem eqA_u {p q : Nat} (hp : Cn p) (hq : Cn q) :
    eqA 1782 (unpack 1782 11 p) (unpack 1782 11 q) = Nat.beq p q :=
  CFSG.KC.BfsPin.eqA_unpack hp hq

theorem ok_spec {p : Nat} (h : ok p = true) :
    Cn p ∧ Cn (pinv p) ∧ permOK 1782 11 (mask 11) (1782 * 11) p (pinv p) = true := by
  unfold ok at h
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  exact ⟨h1, h2, h3⟩

theorem inv_u {a : Array Nat} {P : Nat} (ha : a = unpack 1782 11 P)
    (h : permOK 1782 11 (mask 11) (1782 * 11) P (pinv P) = true) :
    invCand 1782 a = unpack 1782 11 (pinv P) ∧ isInvA 1782 a (invCand 1782 a) = true := by
  obtain ⟨h1, h2⟩ := invEqK_sound (r := pinv P) h
  rw [ha, h1]
  exact ⟨rfl, h2⟩

theorem kL : andB (lettersK 3 suzWordA) (andB (lettersK 3 suzWordB) (andB (lettersK 3 suzWordC)
    (andB (lettersK 3 suzWordD) (andB (lettersK 2 suzWordE1) (andB (lettersK 2 suzWordE2)
    (andB (lettersK 2 suzWordE3) (andB (lettersK 2 suzWordU1) (andB (lettersK 2 suzWordV1)
    (andB (lettersK 2 suzWordU2) (lettersK 2 suzWordV2)))))))))) = true := by
  quickRfl

theorem word_of {S : Array (Array Nat)} {k : Nat} {PS PSI : Nat → Nat} {wd : List Int}
    (hS : S.size = k ∧ ∀ j < k, S[j]! = unpack 1782 11 (PS j))
    (hp : ∀ j < k, permOK 1782 11 (mask 11) (1782 * 11) (PS j) (PSI j) = true)
    (hl : lettersK k wd = true) :
    wordA 1782 S (rawInvs 1782 S) wd = unpack 1782 11 (wordK 1782 11 (mask 11) e PS PSI wd) := by
  refine (wordEqK_sound hS (CFSG.KS.Raw.Orb.allN_iff.2 hp) ?_).1
  unfold wordEqK
  simp only [bAnd_iff, hsz, hl, true_and]
  exact Nat.beq_refl _

theorem tri_bind : bTriple.size = 3 ∧ ∀ j < 3, bTriple[j]! = unpack 1782 11 (triS j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · change bTriple[0]! = unpack 1782 11 B0
    simpa [bTriple] using b0Arr_eq
  · change bTriple[1]! = unpack 1782 11 B1
    simpa [bTriple] using b1Arr_eq
  · change bTriple[2]! = unpack 1782 11 V
    simpa [bTriple] using vArr_eq

theorem tri_p : ∀ j < 3, permOK 1782 11 (mask 11) (1782 * 11) (triS j) (triSI j) = true :=
  fun j hj => CFSG.KS.Raw.Orb.allN_iff.1 tri_perms j hj

theorem w3_eq {wd : List Int} (hl : lettersK 3 wd = true) :
    suzArr wd = unpack 1782 11 (W3 wd) := by
  unfold suzArr W3
  exact word_of tri_bind tri_p hl

theorem letters : lettersK 3 suzWordA = true ∧ lettersK 3 suzWordB = true ∧
    lettersK 3 suzWordC = true ∧ lettersK 3 suzWordD = true ∧ lettersK 2 suzWordE1 = true ∧
    lettersK 2 suzWordE2 = true ∧ lettersK 2 suzWordE3 = true ∧ lettersK 2 suzWordU1 = true ∧
    lettersK 2 suzWordV1 = true ∧ lettersK 2 suzWordU2 = true ∧ lettersK 2 suzWordV2 = true := by
  have h := kL
  simp only [andB_iff] at h
  exact h

theorem inv_parts : (Cn PA ∧ Cn (pinv PA) ∧ permOK 1782 11 (mask 11) (1782 * 11) PA (pinv PA) = true) ∧
    (Cn PB ∧ Cn (pinv PB) ∧ permOK 1782 11 (mask 11) (1782 * 11) PB (pinv PB) = true) := by
  have h := kInv
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, -⟩ := andB_iff.1 h
  exact ⟨ok_spec h1, ok_spec h2⟩

theorem pa_eq : suzArrA = unpack 1782 11 PA := by
  unfold suzArrA PA
  exact w3_eq letters.1

theorem pb_eq : suzArrB = unpack 1782 11 PB := by
  unfold suzArrB PB
  exact w3_eq letters.2.1

theorem ab_bind : suzArrAB.size = 2 ∧ ∀ j < 2, suzArrAB[j]! = unpack 1782 11 (sel2 PA PB j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => exact pa_eq
  | 1, _ => exact pb_eq

theorem ab_p : ∀ j < 2, permOK 1782 11 (mask 11) (1782 * 11) (sel2 PA PB j)
    (sel2 (pinv PA) (pinv PB) j) = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact inv_parts.1.2.2
  | 1, _ => exact inv_parts.2.2.2

theorem abi_eq : suzArrABi = rawInvs 1782 suzArrAB := by
  unfold suzArrABi suzArrAi suzArrBi
  simp [rawInvs, suzArrAB]

theorem wk_eq {wd : List Int} (hl : lettersK 2 wd = true) :
    suzArrWord wd = unpack 1782 11 (WK wd) := by
  unfold suzArrWord WK
  rw [abi_eq]
  exact word_of ab_bind ab_p hl

theorem all_parts :
    (Cn (WK suzWordU1) ∧ Cn (pinv (WK suzWordU1)) ∧
      permOK 1782 11 (mask 11) (1782 * 11) (WK suzWordU1) (pinv (WK suzWordU1)) = true) ∧
    (Cn (WK suzWordV1) ∧ Cn (pinv (WK suzWordV1)) ∧
      permOK 1782 11 (mask 11) (1782 * 11) (WK suzWordV1) (pinv (WK suzWordV1)) = true) ∧
    (Cn (WK suzWordU2) ∧ Cn (pinv (WK suzWordU2)) ∧
      permOK 1782 11 (mask 11) (1782 * 11) (WK suzWordU2) (pinv (WK suzWordU2)) = true) ∧
    (Cn (WK suzWordV2) ∧ Cn (pinv (WK suzWordV2)) ∧
      permOK 1782 11 (mask 11) (1782 * 11) (WK suzWordV2) (pinv (WK suzWordV2)) = true) ∧
    (Cn (W3 suzWordC) ∧ Cn (pinv (W3 suzWordC)) ∧
      permOK 1782 11 (mask 11) (1782 * 11) (W3 suzWordC) (pinv (W3 suzWordC)) = true) ∧
    (Cn (W3 suzWordD) ∧ Cn (pinv (W3 suzWordD)) ∧
      permOK 1782 11 (mask 11) (1782 * 11) (W3 suzWordD) (pinv (W3 suzWordD)) = true) ∧
    Cn (WK suzWordE1) ∧ Cn (WK suzWordE2) ∧ Cn (WK suzWordE3) ∧ Cn (SuzTP 0) := by
  have h := kInv
  obtain ⟨-, h⟩ := andB_iff.1 h
  obtain ⟨-, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h⟩ := andB_iff.1 h
  obtain ⟨h8, h⟩ := andB_iff.1 h
  obtain ⟨h9, h⟩ := andB_iff.1 h
  obtain ⟨h10, h⟩ := andB_iff.1 h
  obtain ⟨h11, h12⟩ := andB_iff.1 h
  exact ⟨ok_spec h3, ok_spec h4, ok_spec h5, ok_spec h6, ok_spec h7, ok_spec h8, h9, h10, h11, h12⟩

theorem lettersC : suzPinLetters = true := by
  unfold suzPinLetters
  rw [pa_eq, pb_eq, CFSG.KC.L34KSnd.size_unpack, CFSG.KC.L34KSnd.size_unpack]
  decide

theorem e8 : suzE8Check = true := by
  obtain ⟨-, -, -, -, -, -, ca, cb, cc, -⟩ := all_parts
  have h := kE8
  rw [strictB_app, strictB_app, strictB_app] at h
  unfold suzE8Check
  dsimp only
  rw [wk_eq letters.2.2.2.2.1, wk_eq letters.2.2.2.2.2.1, wk_eq letters.2.2.2.2.2.2.1, hidA]
  generalize WK suzWordE1 = a at ca h ⊢
  generalize WK suzWordE2 = b at cb h ⊢
  generalize WK suzWordE3 = c at cc h ⊢
  have ce := cE
  generalize e = z at ce h ⊢
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h⟩ := andB_iff.1 h
  obtain ⟨h5, h⟩ := andB_iff.1 h
  obtain ⟨h6, h⟩ := andB_iff.1 h
  obtain ⟨h7, h⟩ := andB_iff.1 h
  obtain ⟨h8, h⟩ := andB_iff.1 h
  obtain ⟨h9, h⟩ := andB_iff.1 h
  obtain ⟨h10, h⟩ := andB_iff.1 h
  obtain ⟨h11, h⟩ := andB_iff.1 h
  obtain ⟨h12, h13⟩ := andB_iff.1 h
  rw [notB_iff] at h7 h8 h9 h10 h11 h12 h13
  rw [compA_u ca ca, compA_u cb cb, compA_u cc cc, compA_u ca cb, compA_u cb ca, compA_u ca cc,
    compA_u cc ca, compA_u cb cc, compA_u cc cb, eqA_u (cpc ca ca) ce, eqA_u (cpc cb cb) ce,
    eqA_u (cpc cc cc) ce, eqA_u (cpc ca cb) (cpc cb ca), eqA_u (cpc ca cc) (cpc cc ca),
    eqA_u (cpc cb cc) (cpc cc cb), eqA_u ca ce, eqA_u cb ce, eqA_u cb ca, eqA_u cc ce, eqA_u cc ca,
    eqA_u cc cb, eqA_u cc (cpc ca cb), h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13]
  rfl

theorem comm_u {u v t : Array Nat} {U V T : Nat} (hu : u = unpack 1782 11 U)
    (hv : v = unpack 1782 11 V) (ht : t = unpack 1782 11 T)
    (pu : Cn U ∧ Cn (pinv U) ∧ permOK 1782 11 (mask 11) (1782 * 11) U (pinv U) = true)
    (pv : Cn V ∧ Cn (pinv V) ∧ permOK 1782 11 (mask 11) (1782 * 11) V (pinv V) = true)
    (cT : Cn T) (h : Nat.beq (CA U V) T = true) : suzCommOK u v t = true := by
  obtain ⟨cU, cUI, pU⟩ := pu
  obtain ⟨cV, cVI, pV⟩ := pv
  have iu := inv_u hu pU
  have iv := inv_u hv pV
  unfold suzCommOK suzCommArr
  rw [iu.2, iv.2, iu.1, iv.1, hu, hv, ht, compA_u cU cV, compA_u (cpc cU cV) cUI,
    compA_u (cpc (cpc cU cV) cUI) cVI, eqA_u (cpc (cpc (cpc cU cV) cUI) cVI) cT]
  unfold CA at h
  rw [h]
  rfl

theorem perf : suzPerfCheck = true := by
  obtain ⟨pu1, pv1, pu2, pv2, -⟩ := all_parts
  have h := kPerf
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  unfold suzPerfCheck
  rw [comm_u (wk_eq letters.2.2.2.2.2.2.2.1) (wk_eq letters.2.2.2.2.2.2.2.2.1) pa_eq pu1 pv1
      inv_parts.1.1 h1,
    comm_u (wk_eq letters.2.2.2.2.2.2.2.2.2.1) (wk_eq letters.2.2.2.2.2.2.2.2.2.2) pb_eq pu2 pv2
      inv_parts.2.1 h2]
  rfl

theorem t0_eq : tArr 0 = unpack 1782 11 (SuzTP 0) := (rep_facts (i := 0) (by decide)).1

theorem commC : suzCommCheck = true := by
  obtain ⟨-, -, -, -, pC, pD, -, -, -, cT⟩ := all_parts
  have cC := pC.1
  have cD := pD.1
  have h := kComm
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h
  have eC := w3_eq letters.2.2.1
  have eD := w3_eq letters.2.2.2.1
  unfold suzCommCheck
  rw [comm_u eC eD t0_eq pC pD cT h3, eC, eD, t0_eq, compA_u cC cT, compA_u cT cC, compA_u cD cT,
    compA_u cT cD, eqA_u (cpc cC cT) (cpc cT cC), eqA_u (cpc cD cT) (cpc cT cD)]
  unfold pc at h1 h2
  unfold pc
  rw [h1, h2]
  rfl

theorem hd_parts : PK.cnt = 20160 ∧ PK.k = 2 ∧ penumHdK e PK.cnt 20160 PK.T PK.PL = true ∧
    PK.G 0 = PA ∧ PK.G 1 = PB := by
  have h := kHd
  obtain ⟨h1, h⟩ := andB_iff.1 h
  obtain ⟨h2, h⟩ := andB_iff.1 h
  obtain ⟨h3, h⟩ := andB_iff.1 h
  obtain ⟨h4, h5⟩ := andB_iff.1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, h3, Nat.eq_of_beq_eq_true h4,
    Nat.eq_of_beq_eq_true h5⟩

theorem gensK : GensOK 1782 11 2 PK.G suzArrAB := by
  refine ⟨rfl, fun j hj => ?_⟩
  match j, hj with
  | 0, _ => rw [hd_parts.2.2.2.1]; exact ⟨pa_eq, inv_parts.1.1⟩
  | 1, _ => rw [hd_parts.2.2.2.2]; exact ⟨pb_eq, inv_parts.2.1⟩

theorem ptK : ∀ i < PK.cnt, penumPtK 1782 11 (mask 11) (1782 * 11) false PK.G PK.GI 2 PK.cnt PK.T
    PK.PL PK.POS PK.SRT PK.SRI i = true := by
  intro i hi
  have hi' : i < 20160 := hd_parts.1 ▸ hi
  have hs : i / 32 < 630 := by omega
  exact penumSl_spec (kSlAll (i / 32) hs) i (by change i / 32 * 32 ≤ i; omega)
    (by change i < i / 32 * 32 + 32; omega) hi

theorem encK : enumBFS 1782 suzArrAB 20160 = penumRec 1782 11 PK.cnt PK.T PK.PL ∧
    enumOK 1782 suzArrAB (penumRec 1782 11 PK.cnt PK.T PK.PL) = true :=
  penumK_left_sound hsz gensK hd_parts.2.2.1 ptK

theorem kc : suzKCheck = true := by
  unfold suzKCheck enumOf
  rw [encK.1, encK.2, penumRec_eq, Array.size_ofFn, hd_parts.1]
  rfl

theorem check26990 : suzPinCheck = true := by
  unfold suzPinCheck
  rw [lettersC, e8, perf, commC, kc]
  rfl

end CertificateChecks.KernelSpor.S26990

end

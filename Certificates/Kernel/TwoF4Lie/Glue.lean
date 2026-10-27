module

public import Certificates.Data.TwoF4LieCheck
public import CFSG.Sporadic.Schreier.TitsActionCheckInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
public import CFSG.Sporadic.Schreier.TitsAction
public import Mathlib.Logic.Relation
import Certificates.Kernel.TwoF4Lie.Checks
import Certificates.Kernel.TwoF4Lie.Range
import CFSG.Certificates.Kernel.TwoF4LieSound
import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.Quasithin.Recognition.RuTypeJ47Cert
import CFSG.Sporadic.Schreier.TitsCentral
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public import CFSG.Sporadic.Schreier.TitsCertCheckInputs
public import CFSG.Sporadic.Schreier.TitsLocalCheckInputs
public import CFSG.Sporadic.Schreier.TitsPrimCheckInputs
public meta import CFSG.Sporadic.Schreier.TitsLocal
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import CFSG.Certificates.NativeInvariantMerge
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public import CFSG.Sporadic.Schreier.TitsStabCheckInputs
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public import Certificates.Data.RuTypeJ47Inputs
public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsInputs
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public import CFSG.Quasithin.Recognition.CertTits
public import CFSG.Blueprint.Catalog
public import CFSG.Quasithin.Recognition.CertPermOuter
public import CFSG.Quasithin.Recognition.CertTitsOuterInputs
public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Sporadic.Schreier.TitsOrbit
public import CFSG.Quasithin.Recognition.CertMergeTargets
public import CFSG.Quasithin.Recognition.CertDataTitsOvergroup
public import CFSG.Quasithin.Recognition.CertTitsOvergroupCheckInputs
public import Std.Data.HashMap
public import CFSG.Sporadic.Schreier.TitsCentralCheck
public import CFSG.Quasithin.Recognition.CertTitsJCheck
public import CFSG.Quasithin.Recognition.CertVertexTable2
public import CFSG.Quasithin.Recognition.CertTwoF4CheckInputs
public import Certificates.Certificate7092
public import Certificates.Certificate4180Base
public import Certificates.Certificate7050Base

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTwoF4Lie

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.TwoF4LieK CFSG.KD.TwoF4Lie
  CFSG.KC.TwoF4LieSound CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.RuType.J47
  CertificateChecks.KernelMisc
  CertificateChecks.KernelSporSch.TitsAction CertificateChecks.KernelSporSch
  CertificateChecks.KernelSpor.Tits2264 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

open CFSG.Quasithin (twoF4S twoF4S_le_twoF4H)

open scoped Pointwise

local notation "tK" => Certificates.c4180T

local notation "cK" => Certificates.c4180C

local notation "stepK" => Certificates.c4180Step

theorem hF : ∀ h < 4, PR (F h) (titsGen h) := fun h hh => prep_of_rep (by
  change Rep 1755 (unpack 1755 11 (TitsText.F h)) (titsGen h)
  rw [← gen_eq hh]
  exact titsGen_rep hh)

theorem hFI : ∀ h < 4, PR (TGI h) (titsGen h)⁻¹ := fun h hh => by
  obtain ⟨g, hg, hgi⟩ := CFSG.KC.EnumSound.permOK_perm (allN_spec invG h hh)
  rwa [CFSG.KC.EnumSound.prep_unique hg (hF h hh)] at hgi

theorem codes_mem {wd : List ℕ} (hw : CodesOK wd) : wordP titsGen wd ∈ titsA := by
  unfold wordP
  refine Subgroup.list_prod_mem (K := titsA) ?_
  intro x hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
  have h4 : c / 2 - 1 < 4 := by have := hw c hc; omega
  unfold letP
  split_ifs
  · exact titsGen_mem_titsA h4
  · exact titsA.inv_mem (titsGen_mem_titsA h4)

theorem lpK_eq (v : Fin 2925) {k : ℕ} (hk : k < 3) : lpK (3 * v + k) = titsLinePt v k := by
  rw [titsLinePt_val v hk, lp_get (by omega)]

theorem hline (v : Fin 2925) (p : Fin 1755) : p ∈ titsLine v ↔ ∃ k < 3, lpK (3 * v + k) = p := by
  constructor
  · intro h
    obtain ⟨k, hk, e⟩ := exists_linePt_of_mem h
    exact ⟨k, hk, by rw [lpK_eq v hk, e]⟩
  · rintro ⟨k, hk, e⟩
    have e' : titsLinePt v k = p := Fin.ext (by rw [← lpK_eq v hk, e])
    rw [← e']
    exact linePt_mem v hk

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (c && t || !c && e) := by
  cases c <;> simp

theorem onL0_iff (p : Fin 1755) : onL0 lpK p = true ↔ p ∈ titsLine 0 := by
  rw [hline 0 p]
  unfold onL0
  simp only [bIf_eq, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    CFSG.KC.EnumSound.beq_iff]
  constructor
  · rintro (h | ⟨-, h | ⟨-, h⟩⟩)
    · exact ⟨0, by norm_num, by simpa using h.symm⟩
    · exact ⟨1, by norm_num, by simpa using h.symm⟩
    · exact ⟨2, by norm_num, by simpa using h.symm⟩
  · rintro ⟨k, hk, e⟩
    simp only [Fin.isValue, Fin.val_zero, Nat.mul_zero, Nat.zero_add] at e
    by_cases h0 : (p : ℕ) = lpK 0
    · exact Or.inl h0
    · right
      refine ⟨by cases h : Nat.beq p (lpK 0) <;> simp_all [CFSG.KC.EnumSound.beq_iff], ?_⟩
      by_cases h1 : (p : ℕ) = lpK 1
      · exact Or.inl h1
      · right
        refine ⟨by cases h : Nat.beq p (lpK 1) <;> simp_all [CFSG.KC.EnumSound.beq_iff], ?_⟩
        interval_cases k <;> simp_all

theorem lpK_lt {k : ℕ} (hk : k < 3) : lpK k < 1755 := by
  have := lpK_eq 0 hk
  simp only [Fin.isValue, Fin.val_zero, Nat.mul_zero, Nat.zero_add] at this
  rw [this]
  exact (titsLinePt 0 k).2

theorem lpK_lt8775 {i : ℕ} (hi : i < 8775) : lpK i < 1755 := by
  have e := lpK_eq ⟨i / 3, by omega⟩ (Nat.mod_lt i (by norm_num : 3 > 0))
  simp only [Nat.div_add_mod] at e
  rw [e]
  exact (titsLinePt _ _).2

theorem stabS_sound {P : ℕ} {x : Pm} (hP : PR P x) (h : stabS lpK (gp P) = true) :
    x 0 = 0 ∧ x • titsLine 0 = titsLine 0 := by
  unfold stabS at h
  simp only [bAnd_eq', Bool.and_eq_true, CFSG.KC.EnumSound.beq_iff] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨Fin.ext (by rw [← gp_eq hP 0]; exact h0), smul_eq_of_maps fun p hp => ?_⟩
  obtain ⟨k, hk, e⟩ := (hline 0 p).1 hp
  simp only [Fin.isValue, Fin.val_zero, Nat.mul_zero, Nat.zero_add] at e
  rw [← onL0_iff, ← gp_eq hP p, ← e]
  interval_cases k
  · exact h1
  · exact h2
  · exact h3

theorem dSW : sW.length = 4 ∧ ∀ w ∈ sW, ∀ c ∈ w, 2 ≤ c ∧ c < 10 := by decide +kernel

theorem dTC : (∀ c ∈ tW, 2 ≤ c ∧ c < 10) ∧ (∀ c ∈ cW, 2 ≤ c ∧ c < 10) ∧
    tW = [8, 6, 8, 2, 8, 6, 9] ∧ cW = [4, 6, 5, 6, 4, 6, 4, 6, 6, 2] := by decide +kernel

theorem dA : aR.length = 64 ∧ ∀ r ∈ aR, r.tail.headD 0 < 4 := by decide +kernel

theorem dB : bR.length = 64 ∧ ∀ r ∈ bR, r.tail.headD 0 < 5 := by decide +kernel

theorem dU : uG.length = 5 ∧ ∀ r ∈ uG, r.headD 0 < 64 ∧ r.getD 1 0 < 4 ∧ r.getD 2 0 < 64 := by
  decide +kernel

theorem dC : (aC.take 32).length = 32 ∧ (aC.drop 32).length = 32 ∧
    ∀ i < 32, ((aC.take 32).getD i []).length = 64 ∧ ((aC.drop 32).getD i []).length = 64 := by
  decide +kernel

theorem dF : fN.length = 141 ∧ ∀ r ∈ fN, r.getD 0 0 < 64 ∧ r.getD 1 0 < 64 ∧ r.getD 2 0 < 64 ∧
    r.getD 3 0 < 64 ∧ ∀ c ∈ r.drop 4, 2 ≤ c ∧ c < 10 := by decide +kernel

theorem dR : r0.headD 0 < 64 ∧ r0.tail.headD 0 < 64 ∧ r1.headD 0 < 64 ∧ r1.tail.headD 0 < 64 :=
  by decide +kernel

theorem dBase : ∀ p ∈ base, p < 1755 := by decide +kernel

theorem dPfl : ∀ v ∈ pflL, v < 2925 := by decide +kernel

theorem twoF4S_le_A {x : Pm} (hx : x ∈ twoF4S) : x ∈ titsA := by
  exact mem_A_of_mem_twoF4H (twoF4S_le_twoF4H hx)

theorem mem_S_of {x : Pm} (hA : x ∈ titsA) (h : x 0 = 0 ∧ x • titsLine 0 = titsLine 0) :
    x ∈ twoF4S :=
  (mem_twoF4S_iff hA).2 h

theorem sEl : ∀ j < 4, ∃ x ∈ twoF4S, PR (TS j) x := by
  intro j hj
  have hj' : j < sW.length := by rw [dSW.1]; exact hj
  have h := (allL_iff sW 0).1 sGen j hj'
  rw [Nat.zero_add, bAnd_eq', Bool.and_eq_true] at h
  have hc : CodesOK sW[j] := dSW.2 _ (List.getElem_mem hj')
  have hP : PR (TS j) (wordP titsGen sW[j]) := by
    rw [Nat.eq_of_beq_eq_true h.1]
    exact wN_prep hF hFI _ hc
  exact ⟨_, mem_S_of (codes_mem hc) (stabS_sound hP h.2), hP⟩

theorem aEl : ∀ i < 64, ∃ x ∈ twoF4S, PR (TA i) x := by
  intro i hi
  exact treeK_sound sEl dA.2 treeA i (by rw [dA.1]; exact hi)

noncomputable def aE (i : ℕ) : Pm := if h : i < 64 then (aEl i h).choose else 1

theorem aE_spec {i : ℕ} (hi : i < 64) : aE i ∈ twoF4S ∧ PR (TA i) (aE i) := by
  rw [aE, dif_pos hi]
  exact (aEl i hi).choose_spec

theorem uEl : ∀ k < 5, ∃ x ∈ twoF4S, PR (TU k) x := by
  intro k hk
  refine ugK_sound (fun q hq => ⟨_, (aE_spec hq).1, (aE_spec hq).2⟩) sEl dU.2
    (fun k hk i hi => ?_) ugB k (by rw [dU.1]; exact hk)
  rw [dU.1] at hk
  have := allN_spec (allN_spec uRange k hk) i hi
  exact Nat.le_of_ble_eq_true this

theorem bEl : ∀ j < 64, ∃ x ∈ twoF4S, PR (TB j) x := by
  intro j hj
  exact treeK_sound uEl dB.2 treeB j (by rw [dB.1]; exact hj)

noncomputable def bE (j : ℕ) : Pm := if h : j < 64 then (bEl j h).choose else 1

theorem bE_spec {j : ℕ} (hj : j < 64) : bE j ∈ twoF4S ∧ PR (TB j) (bE j) := by
  rw [bE, dif_pos hj]
  exact (bEl j hj).choose_spec

theorem bfix : ∀ j < 64, ∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 → bE j p = p := by
  intro j hj p hp
  have := fixAll_sound (allN_spec fixB j hj) p hp
  exact Fin.ext (by rw [← gp_eq (bE_spec hj).2 p]; exact this)

theorem adist : ∀ i < 64, ∀ i' < 64,
    (∀ p : Fin 1755, (p : ℕ) ∈ base.take 4 → aE i p = aE i' p) → i = i' := by
  intro i hi i' hi' h
  refine distK_sound distA i hi i' hi' fun p hp => ?_
  have hp' : p < 1755 := dBase p (List.mem_of_mem_take hp)
  have := h ⟨p, hp'⟩ hp
  rw [gp_eq (aE_spec hi).2 ⟨p, hp'⟩, gp_eq (aE_spec hi').2 ⟨p, hp'⟩, this]

theorem bdist : ∀ j < 64, ∀ j' < 64,
    (∀ p : Fin 1755, (p : ℕ) ∈ base.drop 4 → bE j p = bE j' p) → j = j' := by
  intro j hj j' hj' h
  refine distK_sound distB j hj j' hj' fun p hp => ?_
  have hp' : p < 1755 := dBase p (List.mem_of_mem_drop hp)
  have := h ⟨p, hp'⟩ hp
  rw [gp_eq (bE_spec hj).2 ⟨p, hp'⟩, gp_eq (bE_spec hj').2 ⟨p, hp'⟩, this]

theorem cover (hS : Nat.card twoF4S = 4096) : ∀ x ∈ twoF4S, ∃ i < 64, ∃ j < 64, x = aE i * bE j :=
  factor_cover hS (fun i hi => (aE_spec hi).1)
    (fun j hj => (bE_spec hj).1) bfix adist bdist

theorem faithful (hS : Nat.card twoF4S = 4096) {x y : Pm} (hx : x ∈ twoF4S) (hy : y ∈ twoF4S)
    (h : ∀ p : Fin 1755, (p : ℕ) ∈ base → x p = y p) : x = y :=
  factor_faithful hS (fun i hi => (aE_spec hi).1)
    (fun j hj => (bE_spec hj).1) bfix adist bdist hx hy h

theorem prep_t : PR (TTC 0) tK := by
  have h := tc
  rw [bAnd_eq', Bool.and_eq_true] at h
  rw [Nat.eq_of_beq_eq_true h.1]
  have e : wordP titsGen tW = tK := by
    rw [dTC.2.2.1]
    simp [wordP, letP, Certificates.c4180T, mul_assoc]
  rw [← e]
  exact wN_prep hF hFI _ dTC.1

theorem prep_c : PR (TTC 1) cK := by
  have h := tc
  rw [bAnd_eq', Bool.and_eq_true] at h
  rw [Nat.eq_of_beq_eq_true h.2]
  have e : wordP titsGen cW = cK := by
    rw [dTC.2.2.2]
    simp [wordP, letP, Certificates.c4180C, mul_assoc]
  rw [← e]
  exact wN_prep hF hFI _ dTC.2.1

theorem prep_z : PR TitsZ titsZ :=
  prep_of_rep (by rw [← TitsCommon.z_eq]; exact titsZ_rep)

theorem t_mem : tK ∈ twoF4S := by
  have h := roots
  rw [bAnd_eq', Bool.and_eq_true] at h
  have hP := prep_mul (aE_spec dR.2.2.1).2 (bE_spec dR.2.2.2).2
  rw [Nat.eq_of_beq_eq_true h.2] at hP
  rw [CFSG.KC.EnumSound.prep_unique prep_t hP]
  exact twoF4S.mul_mem (aE_spec dR.2.2.1).1 (bE_spec dR.2.2.2).1

theorem tFacts' : tK * tK = 1 ∧
    (Finset.univ.filter fun p : Fin 1755 => tK p = p).card = 27 ∧
    (Finset.univ.filter fun p : Fin 1755 => titsZ p = p).card = 91 := by
  have h := tFacts
  simp only [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, -, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hP := prep_mul prep_t prep_t
    rw [Nat.eq_of_beq_eq_true h1] at hP
    exact CFSG.KC.EnumSound.prep_unique hP prep_idP
  · rw [fixCnt_sound prep_t]
    exact Nat.eq_of_beq_eq_true h3
  · rw [fixCnt_sound prep_z]
    exact Nat.eq_of_beq_eq_true h4

theorem cFacts' : cK ^ 3 = 1 ∧ cK ≠ 1 ∧
    cK * tK = tK * cK := by
  have h := cFacts
  simp only [bAnd_eq', Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun hc => ?_, ?_⟩
  · have hP := prep_mul prep_c (prep_mul prep_c prep_c)
    rw [Nat.eq_of_beq_eq_true h1] at hP
    have := CFSG.KC.EnumSound.prep_unique hP prep_idP
    rw [pow_succ, pow_two, mul_assoc]
    exact this
  · have hne : Nat.beq (TTC 1) idP = false := by
      cases e : Nat.beq (TTC 1) idP
      · rfl
      · rw [e] at h2
        exact absurd h2 (by decide)
    have hshr : TTC 1 >>> (1755 * 11) = 0 := by
      have ht := tc
      rw [bAnd_eq', Bool.and_eq_true] at ht
      have e : wN F TGI [4, 6, 5, 6, 4, 6, 4, 6, 6, 2] =
          mul (lett F TGI 4) (wN F TGI [6, 5, 6, 4, 6, 4, 6, 6, 2]) :=
        strictN_eq' (wN F TGI [6, 5, 6, 4, 6, 4, 6, 6, 2]) (fun T => mul (lett F TGI 4) T)
      rw [Nat.eq_of_beq_eq_true ht.2, dTC.2.2.2, e]
      exact PF.pcomp_shr _ _ (by norm_num) (by norm_num)
    have heq : TTC 1 = idP := PF.eq_of_fields (by norm_num) hshr
      (PF.pidn_shr (by norm_num) (by norm_num)) fun i hi =>
        (prep_c ⟨i, hi⟩).trans ((congrArg (fun f : Pm => ((f ⟨i, hi⟩ : Fin 1755) : ℕ)) hc).trans
          (prep_idP ⟨i, hi⟩).symm)
    rw [heq, Nat.beq_refl] at hne
    exact absurd hne (by decide)
  · have hP := prep_mul prep_c prep_t
    rw [Nat.eq_of_beq_eq_true h3] at hP
    exact CFSG.KC.EnumSound.prep_unique hP (prep_mul prep_t prep_c)

theorem pflFacts : (∀ p ∈ titsLine 0, tK p = p) ∧
    (∀ p ∈ titsLine 0, ∃ w : Fin 2925, (∀ q ∈ titsLine w, tK q = q) ∧ w ≠ 0 ∧
      p ∈ titsLine w) ∧
    ∀ v : Fin 2925, (∀ q ∈ titsLine v, tK q = q) →
      (∀ p ∈ titsLine v, ∃ w : Fin 2925, (∀ q ∈ titsLine w, tK q = q) ∧ w ≠ v ∧
        p ∈ titsLine w) → v = 0 :=
  pflK_sound prep_t hline dPfl (fun _ hi => lpK_lt8775 hi) pfl

abbrev QS (c : Pm) : Prop := c 0 = 0 ∨ c • titsLine 0 = titsLine 0

def Reach (k : ℕ) : Prop := ∀ i < 64, ∀ j < 64, 64 * i + j = k →
  Relation.ReflTransGen (StepR twoF4S titsA QS) titsZ (aE i * bE j) ∨
    Relation.ReflTransGen (StepR twoF4S titsA QS) tK (aE i * bE j)

theorem headD_eq (r : List ℕ) : r.headD 0 = r.getD 0 0 := by cases r <;> rfl

theorem tail_headD_eq (r : List ℕ) : r.tail.headD 0 = r.getD 1 0 := by
  rcases r with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> rfl

theorem root0_eq : aE (r0.headD 0) * bE (r0.tail.headD 0) = titsZ := by
  have h := roots
  rw [bAnd_eq', Bool.and_eq_true] at h
  have hP := prep_mul (aE_spec dR.1).2 (bE_spec dR.2.1).2
  rw [Nat.eq_of_beq_eq_true h.1] at hP
  exact CFSG.KC.EnumSound.prep_unique hP prep_z

theorem root1_eq : aE (r1.headD 0) * bE (r1.tail.headD 0) = tK := by
  have h := roots
  rw [bAnd_eq', Bool.and_eq_true] at h
  have hP := prep_mul (aE_spec dR.2.2.1).2 (bE_spec dR.2.2.2).2
  rw [Nat.eq_of_beq_eq_true h.2] at hP
  exact CFSG.KC.EnumSound.prep_unique hP prep_t

theorem aE_zero : aE 0 = 1 := by
  have := treeK_zero treeA (by rw [dA.1]; norm_num)
  have hP := (aE_spec (by norm_num : 0 < 64)).2
  rw [this] at hP
  exact CFSG.KC.EnumSound.prep_unique hP prep_idP

theorem bE_zero : bE 0 = 1 := by
  have := treeK_zero treeB (by rw [dB.1]; norm_num)
  have hP := (bE_spec (by norm_num : 0 < 64)).2
  rw [this] at hP
  exact CFSG.KC.EnumSound.prep_unique hP prep_idP

theorem reach_root0 : Reach (nodeOf r0) := by
  intro i hi j hj e
  have hr := dR
  have hi' : i = r0.headD 0 := by unfold nodeOf at e; simp only [Nat.add_eq, Nat.mul_eq] at e; omega
  have hj' : j = r0.tail.headD 0 := by unfold nodeOf at e; simp only [Nat.add_eq, Nat.mul_eq] at e; omega
  subst hi' hj'
  have h := roots
  rw [bAnd_eq', Bool.and_eq_true] at h
  have hP := prep_mul (aE_spec hi).2 (bE_spec hj).2
  rw [Nat.eq_of_beq_eq_true h.1] at hP
  rw [CFSG.KC.EnumSound.prep_unique hP prep_z]
  exact Or.inl Relation.ReflTransGen.refl

theorem reach_root1 : Reach (nodeOf r1) := by
  intro i hi j hj e
  have hr := dR
  have hi' : i = r1.headD 0 := by unfold nodeOf at e; simp only [Nat.add_eq, Nat.mul_eq] at e; omega
  have hj' : j = r1.tail.headD 0 := by unfold nodeOf at e; simp only [Nat.add_eq, Nat.mul_eq] at e; omega
  subst hi' hj'
  have h := roots
  rw [bAnd_eq', Bool.and_eq_true] at h
  have hP := prep_mul (aE_spec hi).2 (bE_spec hj).2
  rw [Nat.eq_of_beq_eq_true h.2] at hP
  rw [CFSG.KC.EnumSound.prep_unique hP prep_t]
  exact Or.inr Relation.ReflTransGen.refl

def RowOK (r : List ℕ) : Prop := r.getD 0 0 < 64 ∧ r.getD 1 0 < 64 ∧ r.getD 2 0 < 64 ∧
  r.getD 3 0 < 64 ∧ ∀ c ∈ r.drop 4, 2 ≤ c ∧ c < 10

theorem reach_step (hS : Nat.card twoF4S = 4096) (r : List ℕ) (hr : RowOK r) (h : rowF F TGI TA TB lpK base r = true)
    (hp : Reach (Nat.add (Nat.mul 64 (r.getD 2 0)) (r.getD 3 0))) : Reach (nodeOf r) := by
  obtain ⟨h0, h1, h2, h3, hc⟩ := hr
  intro i hi j hj e
  have hi' : i = r.getD 0 0 := by
    unfold nodeOf at e; rw [headD_eq, tail_headD_eq] at e; simp only [Nat.add_eq, Nat.mul_eq] at e
    omega
  have hj' : j = r.getD 1 0 := by
    unfold nodeOf at e; rw [headD_eq, tail_headD_eq] at e; simp only [Nat.add_eq, Nat.mul_eq] at e
    omega
  subst hi' hj'
  obtain ⟨hy0, hyL, hyb, hW⟩ := rowF_sound hF hFI hc (aE_spec hi).2 (bE_spec hj).2
    (aE_spec h2).2 (bE_spec h3).2 (fun k hk => lpK_lt hk) h
  have hWA := codes_mem hc
  have hxS := twoF4S.mul_mem (aE_spec hi).1 (bE_spec hj).1
  have hpS := twoF4S.mul_mem (aE_spec h2).1 (bE_spec h3).1
  have hyA : (wordP titsGen (r.drop 4))⁻¹ * (aE (r.getD 0 0) * bE (r.getD 1 0)) *
      wordP titsGen (r.drop 4) ∈ titsA :=
    titsA.mul_mem (titsA.mul_mem (titsA.inv_mem hWA) (twoF4S_le_A hxS)) hWA
  have hyS := mem_S_of hyA ⟨hy0, smul_eq_of_maps fun p hp => (onL0_iff _).1 (hyL p
    ((onL0_iff p).2 hp))⟩
  have hQ : QS (wordP titsGen (r.drop 4)) := by
    rcases hW with hW | hW
    · exact Or.inl hW
    · exact Or.inr (smul_eq_of_maps fun p hp => (onL0_iff _).1 (hW p ((onL0_iff p).2 hp)))
  have hstep := stepR_of_row (M := titsA) (Q := QS) (fun x hx y hy hxy => faithful hS hx hy hxy) hpS
    hxS hWA hQ hyS hyb
  rcases hp _ h2 _ h3 rfl with hz | ht
  · exact Or.inl (hz.tail hstep)
  · exact Or.inr (ht.tail hstep)

theorem rowOK_fN : ∀ r ∈ fN, RowOK r := dF.2

theorem nodeReach (hS : Nat.card twoF4S = 4096) : ∀ k ∈ nodes, Reach k := by
  have hacc0 : ∀ k ∈ [nodeOf r1, nodeOf r0], Reach k := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact reach_root1
    · exact reach_root0
  have h0 := reach_forK (Rw := RowOK) (reach_step hS) (fN.take 71) _
    (fun r hr => rowOK_fN r (List.mem_of_mem_take hr)) hacc0 for0
  have h1 := reach_forK (Rw := RowOK) (reach_step hS) (fN.drop 71) _
    (fun r hr => rowOK_fN r (List.mem_of_mem_drop hr)) (by
      intro k hk
      rcases List.mem_append.1 hk with hk | hk
      · exact h0 k (List.mem_append_right _ (List.mem_reverse.1 hk))
      · exact hacc0 k hk) for1
  intro k hk
  unfold nodes at hk
  rcases List.mem_cons.1 hk with rfl | hk
  · exact reach_root0
  rcases List.mem_cons.1 hk with rfl | hk
  · exact reach_root1
  rw [← List.take_append_drop 71 fN, List.map_append] at hk
  rcases List.mem_append.1 hk with hk | hk
  · exact h0 k (List.mem_append_right _ hk)
  · exact h1 k (List.mem_append_right _ hk)

theorem covNodes : ∀ i < 64, ∀ j < 64, aE i * bE j * (aE i * bE j) ≠ 1 ∨ 64 * i + j = 0 ∨
    64 * i + j ∈ nodes := by
  intro i hi j hj
  have hc : (∃ w < 1755, gp (TA i) (gp (TB j) (gp (TA i) (gp (TB j) w))) ≠ w) ∨
      64 * i + j = 0 ∨ 64 * i + j ∈ nodes := by
    by_cases hi32 : i < 32
    · have := covK_sound cov0 i (by rw [dC.1]; exact hi32) j (by rw [(dC.2.2 i hi32).1]; exact hj)
      simpa using this
    · have := covK_sound cov1 (i - 32) (by rw [dC.2.1]; omega) j
        (by rw [(dC.2.2 (i - 32) (by omega)).2]; exact hj)
      rwa [Nat.add_sub_cancel' (by omega)] at this
  rcases hc with ⟨w, hw, hne⟩ | h | h
  · left
    intro h1
    apply hne
    have e := congrArg (fun f : Pm => (f ⟨w, hw⟩ : ℕ)) h1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at e
    have e1 : gp (TB j) w = ((bE j ⟨w, hw⟩ : Fin 1755) : ℕ) := gp_eq (bE_spec hj).2 ⟨w, hw⟩
    rw [e1, gp_eq (aE_spec hi).2, gp_eq (bE_spec hj).2, gp_eq (aE_spec hi).2]
    exact e
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem covFacts (hS : Nat.card twoF4S = 4096) : ∀ i < 64, ∀ j < 64,
    aE i * bE j * (aE i * bE j) ≠ 1 ∨ 64 * i + j = 0 ∨ Reach (64 * i + j) := by
  intro i hi j hj
  rcases covNodes i hi j hj with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (nodeReach hS _ h))

theorem chainFacts (hS : Nat.card twoF4S = 4096) : ∀ x ∈ titsA, x 0 = 0 → x • titsLine 0 = titsLine 0 → x * x = 1 → x ≠ 1 →
    Relation.ReflTransGen stepK titsZ x ∨
      Relation.ReflTransGen stepK tK x := by
  intro x hxA hx0 hxL h2 h1
  have hmono : ∀ a b, StepR twoF4S titsA QS a b → stepK a b := by
    rintro a b ⟨haS, hbS, c, hcA, hc, rfl⟩
    exact ⟨⟨twoF4S_le_A haS, (mem_twoF4S_iff (twoF4S_le_A haS)).1 haS⟩,
      ⟨twoF4S_le_A hbS, (mem_twoF4S_iff (twoF4S_le_A hbS)).1 hbS⟩, c, hcA, hc, rfl⟩
  have hlift : ∀ {a b : Pm}, Relation.ReflTransGen (StepR twoF4S titsA QS) a b →
      Relation.ReflTransGen stepK a b := by
    intro a b h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact ih.tail (hmono _ _ hbc)
  rcases chain_of_cover (node := Reach) (cover hS) aE_zero bE_zero (covFacts hS)
      (fun i hi j hj h => h i hi j hj rfl) x (mem_S_of hxA ⟨hx0, hxL⟩) h2 h1 with h | h
  · exact Or.inl (hlift h)
  · exact Or.inr (hlift h)

public theorem facts (hS : Nat.card twoF4S = 4096) :
    (tK 0 = 0 ∧ tK • titsLine 0 = titsLine 0 ∧ tK * tK = 1 ∧ tK ≠ 1 ∧
      (Finset.univ.filter fun p : Fin 1755 => tK p = p).card = 27 ∧
      (Finset.univ.filter fun p : Fin 1755 => titsZ p = p).card = 91) ∧
    (cK ^ 3 = 1 ∧ cK ≠ 1 ∧ cK * tK = tK * cK) ∧
    ((∀ p ∈ titsLine 0, tK p = p) ∧
      (∀ p ∈ titsLine 0, ∃ w : Fin 2925, (∀ q ∈ titsLine w, tK q = q) ∧ w ≠ 0 ∧
        p ∈ titsLine w) ∧
      ∀ v : Fin 2925, (∀ q ∈ titsLine v, tK q = q) →
        (∀ p ∈ titsLine v, ∃ w : Fin 2925, (∀ q ∈ titsLine w, tK q = q) ∧ w ≠ v ∧
          p ∈ titsLine w) → v = 0) ∧
    ∀ x ∈ titsA, x 0 = 0 → x • titsLine 0 = titsLine 0 → x * x = 1 → x ≠ 1 →
      Relation.ReflTransGen stepK titsZ x ∨ Relation.ReflTransGen stepK tK x := by
  have hT := (mem_twoF4S_iff (twoF4S_le_A t_mem)).1 t_mem
  obtain ⟨ht2, h27, h91⟩ := tFacts'
  refine ⟨⟨hT.1, hT.2, ht2, fun h => ?_, h27, h91⟩, cFacts', pflFacts, chainFacts hS⟩
  rw [h] at h27
  simp at h27

end CertificateChecks.KernelTwoF4Lie

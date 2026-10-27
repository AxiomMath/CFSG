module

public import Certificates.Kernel.Sporadic.OddCore.SuzCTF0
public import CFSG.Certificates.Kernel.O8ConstrSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzCT

open CFSG.PSL3Four.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native CFSG.KS.Mathieu CFSG.KC.Misc.HexAt
open CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native

theorem sig1_ok : allN 10 (fun j => sigK 54 fix1L (SuzInvT1.F (Nat.add 18 j)) (K1C.S j) (K1I j)) =
    true := by quickRfl

theorem qg_ok : allN 6 (fun j => bAnd(Nat.beq (QE.G j)
    (wordTabK 54 6 (mask 6) (pidn 54 6) K1C.S (lget2 qWords j)),
    canonK 54 6 (mask 6) (54 * 6) (QE.G j))) = true := by quickRfl

theorem qhead : penumHdK (pidn 54 6) QE.cnt 64 QE.T QE.PL = true := by quickRfl

theorem q_norm : allN 10 (fun j => allN 6 (fun i =>
    bAnd(strictB (QP1 (Nat.add (Nat.mul j 6) i)) (fun q => bAnd(Nat.blt q QE.cnt,
      Nat.beq (QE.T q) (pcomp 54 6 (mask 6) (pcomp 54 6 (mask 6) (K1C.S j) (QE.G i)) (K1I j)))),
    strictB (QP2 (Nat.add (Nat.mul j 6) i)) (fun q => bAnd(Nat.blt q QE.cnt,
      Nat.beq (QE.T q) (pcomp 54 6 (mask 6) (pcomp 54 6 (mask 6) (K1I j) (QE.G i))
        (K1C.S j))))))) = true := by
  quickRfl

theorem act_ok : allN 10 (fun j => allN 64 (fun p => strictB (pg 7 (mask 7) (AC.S j) p) (fun q =>
    bAnd(Nat.blt q 64, Nat.beq (QE.T q)
      (pcomp 54 6 (mask 6) (pcomp 54 6 (mask 6) (K1C.S j) (QE.T p)) (K1I j)))))) = true := by
  quickRfl

theorem act_canon : allN 10 (fun j => canonK 64 7 (mask 7) (64 * 7) (AC.S j)) = true := by
  quickRfl

theorem qcomm : allN 6 (fun i => allN 6 (fun j => Nat.beq (pcomp 54 6 (mask 6) (QE.G i) (QE.G j))
    (pcomp 54 6 (mask 6) (QE.G j) (QE.G i)))) = true := by quickRfl

theorem perm1 : allN 18 (fun j => permOK 54 6 (mask 6) (54 * 6) (K1C.S j) (K1C.SI j)) = true := by
  quickRfl

theorem permA : allN 16 (fun j => permOK 64 7 (mask 7) (64 * 7) (AC.S j) (AC.SI j)) = true := by
  quickRfl

theorem prod1 : ((List.range 6).map fun i => rcnt (K1C.LR i)).prod = 1658880 := by decide +kernel

theorem prodA : ((List.range 5).map fun i => rcnt (AC.LR i)).prod = 25920 := by decide +kernel

theorem comp54 {p q : Nat} (hp : canonK 54 6 (mask 6) (54 * 6) p = true)
    (hq : canonK 54 6 (mask 6) (54 * 6) q = true) :
    comp 54 (unpack 54 6 p) (unpack 54 6 q) = unpack 54 6 (pcomp 54 6 (mask 6) p q) :=
  compA_unpack hp hq

theorem sig1 {j : Nat} (hj : j < 10) :
    sigK 54 fix1L (SuzInvT1.F (Nat.add 18 j)) (K1C.S j) (K1I j) = true :=
  allN_spec sig1_ok j hj

theorem kgens1_size : (kGens 1).size = 10 := by
  simp [kGens, CertificateChecks.KernelSpor.SuzInv.gensI1.1]

theorem kgens1_get {j : Nat} (hj : j < 10) : (kGens 1)[j]! = unpack 54 6 (K1C.S j) := by
  rw [getElem!_pos (kGens 1) j (by rw [kgens1_size]; exact hj)]
  simp only [kGens, Array.getElem_map]
  rw [← getElem!_pos (invInnerGenArrs 1) j (by simp [CertificateChecks.KernelSpor.SuzInv.gensI1.1]; omega),
    CertificateChecks.KernelSpor.SuzInv.gensI1.2 j hj, fix_eq1]
  exact restrict_eq fix1_facts.1 fix1_facts.2.1 fix1_facts.2.2 (sig1 hj)

theorem kinvs1_get {j : Nat} (hj : j < 10) : (kInvs 1)[j]! = unpack 54 6 (K1I j) := by
  rw [kInvs, getElem!_pos _ j (by simp [kgens1_size]; omega), Array.getElem_map,
    ← getElem!_pos (kGens 1) j (by rw [kgens1_size]; exact hj), kgens1_get hj, fix_eq1,
    fix1_facts.1]
  exact (invEqK_sound (sig_facts (sig1 hj)).2.1).1

theorem invsK1 : invsOK 54 (kGens 1) (kInvs 1) = true := by
  unfold invsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp [kInvs], ?_⟩
  unfold allBelow
  rw [all_range_iff]
  intro k hk
  have hk10 : k < 10 := by rwa [kgens1_size] at hk
  obtain ⟨hc, -, -, hci, hpi, -⟩ := sig_facts (sig1 hk10)
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [kinvs1_get hk10, kgens1_get hk10]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp54 hci hc, idTab54, Nat.eq_of_beq_eq_true hpi]

theorem qwords_lt : ∀ j < 6, ∀ i ∈ qWords.getD j [], i < 10 := by decide

theorem qgens_get {j : Nat} (hj : j < 6) : qGens[j]! = unpack 54 6 (QE.G j) := by
  obtain ⟨he, -⟩ := (bAnd_iff _ _).1 (allN_spec qg_ok j hj)
  rw [qGens, getElem!_pos _ j (by simp; omega), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true he, lget2_eq]
  exact (wordTabK_eq idTab54 base.2.2.2.2.1 _ (fun i hi => by
    have hi10 := qwords_lt j hj i hi
    exact ⟨kgens1_get hi10, (sig_facts (sig1 hi10)).1⟩)).1

theorem qgens_canon {j : Nat} (hj : j < 6) : canonK 54 6 (mask 6) (54 * 6) (QE.G j) = true :=
  ((bAnd_iff _ _).1 (allN_spec qg_ok j hj)).2

theorem qgens_size : qGens.size = 6 := by simp [qGens]

theorem q_ok' : GensOK 54 6 QE.k QE.G qGens :=
  ⟨by rw [qgens_size]; rfl, fun _ hj => ⟨qgens_get hj, qgens_canon hj⟩⟩

theorem qpt_all {i : Nat} (hi : i < QE.cnt) : penumPtK 54 6 (mask 6) (54 * 6) false QE.G QE.GI
    QE.k QE.cnt QE.T QE.PL QE.POS QE.SRT QE.SRI i = true := by
  have e : QE.cnt = 64 := rfl
  exact penumSl_spec q_ok i (Nat.zero_le _) (by omega) hi

theorem q_enum : enumOf 54 qGens 64 = penumRec 54 6 QE.cnt QE.T QE.PL ∧
    enumOK 54 qGens (penumRec 54 6 QE.cnt QE.T QE.PL) = true :=
  penumK_left_sound (cap := 64) base.2.2.2.1 q_ok' qhead (fun _ hi => qpt_all hi)

theorem qrec_get {i : Nat} (hi : i < QE.cnt) :
    (penumRec 54 6 QE.cnt QE.T QE.PL).tabs[i]! = unpack 54 6 (QE.T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem qnormal : normalOK 54 (penumRec 54 6 QE.cnt QE.T QE.PL).tabs (kGens 1) (kInvs 1) qGens =
    true := by
  unfold normalOK
  simp only [Bool.and_eq_true]
  refine ⟨invsK1, ?_⟩
  unfold allBelow
  rw [List.all_eq_true]
  intro j hj
  have hj10 : j < 10 := by simpa [kgens1_size] using List.mem_range.1 hj
  rw [List.all_eq_true]
  intro i hi
  have hi6 : i < 6 := by simpa [qgens_size] using List.mem_range.1 hi
  have hn := allN_spec (allN_spec q_norm j hj10) i hi6
  obtain ⟨n1, n2⟩ := (bAnd_iff _ _).1 hn
  rw [strictB_app'] at n1 n2
  obtain ⟨q1, e1⟩ := (bAnd_iff _ _).1 n1
  obtain ⟨q2, e2⟩ := (bAnd_iff _ _).1 n2
  obtain ⟨hc, -, -, hci, -, -⟩ := sig_facts (sig1 hj10)
  have hg := q_ok'.2 i hi6
  rw [Bool.and_eq_true, kgens1_get hj10, kinvs1_get hj10, hg.1]
  unfold conjTab
  rw [comp54 hc hg.2, comp54 (canonK_pcomp hc hg.2) hci, comp54 hci hg.2,
    comp54 (canonK_pcomp hci hg.2) hc]
  exact ⟨penum_found_sound (fun _ hx => qpt_all hx) (Eq.mp Nat.blt_eq q1)
      (Nat.eq_of_beq_eq_true e1),
    penum_found_sound (fun _ hx => qpt_all hx) (Eq.mp Nat.blt_eq q2) (Nat.eq_of_beq_eq_true e2)⟩

theorem pushStrong_eq (n : Nat) : ∀ (ws : List (List Int)) (S : Array (Array Nat)),
    pushStrong n S ws = CFSG.EvenSmallLie.OmegaEight.pushWords n S ws
  | [], _ => rfl
  | w :: ws, S => by
    rw [pushStrong, CFSG.EvenSmallLie.OmegaEight.pushWords]
    exact pushStrong_eq n ws _

theorem binds1 : Binds 54 6 K1C.S 18 6 K1C.BP k1Strong k1Base := by
  have hp := CFSG.KC.O8.pushWords_eq (kO := 10) (G := kGens 1) (D := k1Words)
    ⟨kgens1_size, fun j hj => kgens1_get hj⟩ K1C.head
  have hb : k1Base.size = 6 ∧ ∀ t < 6, k1Base[t]! = pg 6 (mask 6) K1C.BP t := by decide +kernel
  rw [k1Strong, pushStrong_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, hp.1, hp.2, hb.1, hb.2⟩

theorem qtabs_eq : qTabs = (penumRec 54 6 QE.cnt QE.T QE.PL).tabs := by
  rw [qTabs, q_enum.1]

theorem qtabs_nodup : qTabs.toList.Nodup := by
  rw [qtabs_eq]
  exact (CFSG.ComponentClassification.PSL3Four.treeOK_spec q_enum.2).2.2.1

theorem qtabs_size : qTabs.size = 64 := by
  rw [qtabs_eq]
  simp [penumRec]
  rfl

theorem qtabs_get {p : Nat} (hp : p < 64) : qTabs[p]! = unpack 54 6 (QE.T p) := by
  rw [qtabs_eq]
  exact qrec_get hp

theorem actGens_size' : actGens.size = 10 := by simp [actGens]

theorem actGens_eq {j : Nat} (hj : j < 10) : actGens[j]! = unpack 64 7 (AC.S j) := by
  have hcA := allN_spec act_canon j hj
  apply Array.ext
  · rw [getElem!_pos actGens j (by rw [actGens_size']; exact hj)]
    simp [actGens, unpack]
  · intro p h1 _
    have hp : p < 64 := by
      rw [getElem!_pos actGens j (by rw [actGens_size']; exact hj)] at h1
      simpa [actGens] using h1
    rw [← getElem!_pos _ p h1, ← getElem!_pos (unpack 64 7 (AC.S j)) p (by simp [unpack, hp]),
      CFSG.KC.Misc.PairCount.unpack_get hp]
    have ha := allN_spec (allN_spec act_ok j hj) p hp
    rw [strictB_app'] at ha
    obtain ⟨hq, he⟩ := (bAnd_iff _ _).1 ha
    have hq' := Eq.mp Nat.blt_eq hq
    obtain ⟨hc, -, -, hci, -, -⟩ := sig_facts (sig1 hj)
    have hT := penumPt_canon (qpt_all (i := p) hp)
    have hconj : conjTab 54 (kGens 1)[j]! (kInvs 1)[j]! qTabs[p]! =
        qTabs[pg 7 (mask 7) (AC.S j) p]! := by
      rw [qtabs_get hq', qtabs_get hp, kgens1_get hj, kinvs1_get hj, Nat.eq_of_beq_eq_true he]
      unfold conjTab
      rw [comp54 hc hT, comp54 (canonK_pcomp hc hT) hci]
    rw [getElem!_pos actGens j (by rw [actGens_size']; exact hj)]
    simp only [actGens, Array.getElem_ofFn]
    rw [getElem!_pos _ p (by simpa using hp), Array.getElem_ofFn, hconj,
      getElem!_pos qTabs _ (by rw [qtabs_size]; exact hq'), ← Array.getElem_toList]
    exact qtabs_nodup.idxOf_getElem _ _

theorem bindsA : Binds 64 7 AC.S 16 5 AC.BP actStrong actBase := by
  have hp := CFSG.KC.O8.pushWords_eq (kO := 10) (G := actGens) (D := actWords)
    ⟨actGens_size', fun j hj => actGens_eq hj⟩ AC.head
  have hb : actBase.size = 5 ∧ ∀ t < 5, actBase[t]! = pg 7 (mask 7) AC.BP t := by decide +kernel
  rw [actStrong, pushStrong_eq]
  exact ⟨by norm_num, by norm_num, by norm_num, hp.1, hp.2, hb.1, hb.2⟩

theorem canon_lt7 {p a : Nat} (hp : canonK 64 7 (mask 7) (64 * 7) p = true) (ha : a < 64) :
    pg 7 (mask 7) p a < 64 := by
  unfold canonK at hp
  simp only [bAnd_iff] at hp
  exact Eq.mp Nat.blt_eq (allN_spec hp.2.2 a ha)

theorem facts1 : ((fixList 1).length = 54 ∧ (kGens 1).size = 10 ∧
      invsOK 54 (kGens 1) (kInvs 1) = true ∧ (∀ w ∈ qWords, ∀ j ∈ w, j < 10))
    ∧ (enumOK 54 qGens (enumOf 54 qGens 64) = true ∧ (enumOf 54 qGens 64).tabs.size = 64 ∧
      normalOK 54 (enumOf 54 qGens 64).tabs (kGens 1) (kInvs 1) qGens = true)
    ∧ ((rawChainOK 54 (k1Strong.extract 0 10) k1Strong k1Base
          (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 10 18 k1Words) 4 = true ∧
        (rawOrbitSizes 54 k1Strong k1Base).prod = 1658880) ∧
      (rawChainOK 64 (actStrong.extract 0 10) actStrong actBase
          (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 10 16 actWords) 4 = true ∧
        (rawOrbitSizes 64 actStrong actBase).prod = 25920) ∧
      (∀ k < 10, ∀ p < 64, (actGens[k]!)[p]! < 64) ∧
      (∀ i < 6, ∀ j < 6, comp 54 qGens[i]! qGens[j]! = comp 54 qGens[j]! qGens[i]!)) := by
  refine ⟨⟨by rw [fix_eq1]; exact fix1_facts.1, kgens1_size, invsK1, by decide⟩,
    ⟨by rw [q_enum.1]; exact q_enum.2, by rw [q_enum.1]; simp [penumRec]; rfl,
      by rw [q_enum.1]; exact qnormal⟩,
    ⟨rawChainK_sound (NS := 1) (CH := 54) binds1 K1C.head K1C.hl (by norm_num) K1C.hs, ?_⟩,
    ⟨rawChainK_sound (NS := 1) (CH := 64) bindsA AC.head AC.hl (by norm_num) AC.hs, ?_⟩,
    fun k hk p hp => ?_, fun i hi j hj => ?_⟩
  · rw [rawOrbitSizesK_sound binds1 perm1 K1C.hl]
    exact prod1
  · rw [rawOrbitSizesK_sound bindsA permA AC.hl]
    exact prodA
  · rw [actGens_eq hk, CFSG.KC.Misc.PairCount.unpack_get hp]
    exact canon_lt7 (allN_spec act_canon k hk) hp
  · rw [qgens_get hi, qgens_get hj, comp54 (qgens_canon hi) (qgens_canon hj),
      comp54 (qgens_canon hj) (qgens_canon hi),
      Nat.eq_of_beq_eq_true (allN_spec (allN_spec qcomm i hi) j hj)]

end CertificateChecks.KernelSpor.SuzCT

end

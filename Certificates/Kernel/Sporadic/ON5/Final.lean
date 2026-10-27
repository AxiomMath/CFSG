
module

public import Certificates.Kernel.Sporadic.ON5.Sl
public import Certificates.Kernel.Sporadic.OddCore.ON2129F
public import Certificates.Kernel.Sporadic.ON3.Small
public import CFSG.Certificates.Kernel.Spor.ChainFKSound
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Sporadic.Schreier.ONCheckSmallAuxInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.ChainKSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ON5K.mSlAll CertificateChecks.KernelSpor.ON5K.mSl 20
#kon_join CertificateChecks.KernelSpor.ON5K.dSelAll CertificateChecks.KernelSpor.ON5K.dSelS 20

namespace CertificateChecks.KernelSpor.ON5K

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.CB CFSG.KS.CH CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.KC.BfsPin CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor.ON3 (allBelowN_iff)
open CertificateChecks.KernelSpor.ON2129 (t32Enum_eq szOK32 t32_hd t32_gens t32_pt idTab_eq)

theorem allBelowN_eq (n : Nat) (p : Nat → Bool) : allBelowN n p = allN n p := by
  rw [Bool.eq_iff_iff, allBelowN_iff, CFSG.KS.PK.allN_iff]

theorem comp_unpackG {n w p q : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hq : canonK n w (mask w) (n * w) q = true) :
    comp n (unpack n w p) (unpack n w q) = unpack n w (pcomp n w (mask w) p q) :=
  compA_unpack hp hq

theorem all_comm {n w k : Nat} {G : Nat → Nat} {gens : Array Tab} (hg : GensOK n w k G gens)
    {t : Nat} (ht : canonK n w (mask w) (n * w) t = true) :
    (gens.all fun g => comp n (unpack n w t) g == comp n g (unpack n w t)) =
      allN k fun j => Nat.beq (pcomp n w (mask w) t (G j)) (pcomp n w (mask w) (G j) t) := by
  obtain ⟨hs, hgj⟩ := hg
  rw [Bool.eq_iff_iff, Array.all_eq_true, CFSG.KS.PK.allN_iff]
  constructor
  · intro h j hj
    have := h j (by rw [hs]; exact hj)
    rw [← getElem!_pos gens j (by rw [hs]; exact hj), (hgj j hj).1, comp_unpackG ht (hgj j hj).2,
      comp_unpackG (hgj j hj).2 ht, beq_unpack (canonK_pcomp ht (hgj j hj).2)
        (canonK_pcomp (hgj j hj).2 ht)] at this
    exact this
  · intro h j hj
    have hj' : j < k := by rw [← hs]; exact hj
    have := h j hj'
    rw [← getElem!_pos gens j hj, (hgj j hj').1, comp_unpackG ht (hgj j hj').2,
      comp_unpackG (hgj j hj').2 ht, beq_unpack (canonK_pcomp ht (hgj j hj').2)
        (canonK_pcomp (hgj j hj').2 ht)]
    exact this

theorem pisInv_of {n : Nat} {t : Array Nat} {f fi : Nat → Nat} (hs : t.size = n)
    (hf : ∀ x < n, t[x]! = f x) (hp : ∀ x < n, f x < n ∧ fi (f x) = x) :
    pisInv n t (pinvCand n t) = true := by
  have e := CFSG.KS.PW.arr_ext hs hf
  unfold pisInv
  refine allBelowN_iff.2 fun x hx => ?_
  have hg : (pinvCand n t)[f x]! = fi (f x) := by
    rw [e]
    exact CFSG.KS.CB.pinvCand_get (fun y hy => (hp y hy).1) (fun y hy => (hp y hy).2) (hp x hx).1
  rw [hf x hx, hg, (hp x hx).2]
  simp [(hp x hx).1]

theorem small_parts : (∀ j < 4, ∀ x < 120, dF j x = (Data.D120Generators[j]!)[x]! ∧ dF j x < 120 ∧
      dFI j x < 120 ∧ dFI j (dF j x) = x) ∧
    (∀ j < Data.M120Chain.strongGenerators.size, ∀ x < 120,
      sF j x = (Data.M120Chain.strongGenerators[j]!)[x]! ∧ sF j x < 120 ∧ sFI j x < 120 ∧
      sFI j (sF j x) = x) ∧
    (∀ x < 32, Data.T32z[x]! < 32 ∧ zI x < 32 ∧ zI (Data.T32z[x]!) = x) ∧
    (∀ i < 3, idxOK sF Data.M120Chain.strongGenerators.size sB i (sIDX i) (sLEN i) = true ∧
      cbHead 120 (sMr i) (sB i) (sPTS i) (sPAR i) (sLAB i) = true ∧
      (∀ k < sMr i, cbPt 120 (sMr i) (Nat.mul 2 (sLEN i)) (stepX sF sFI (sIDX i) (sLEN i))
        (sPTS i) (sPOS i) (sPAR i) (sLAB i) k = true) ∧
      ∀ z < 120, cbPos 120 (sMr i) (sPTS i) (sPOS i) z = true) ∧
    ∀ j < 4, siftFull3 120 sPOS sPAR sLAB sMr (fun i => invX sF sFI (sIDX i) (sLEN i)) sB (dF j) =
      true := by
  have h := small_ok
  unfold smallOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun j hj x hx => ?_, fun j hj x hx => ?_, fun x hx => ?_, fun i hi => ?_,
    fun j hj => allN_spec h5 j hj⟩
  · have := allN_spec (allN_spec h1 j hj) x hx
    simp only [bAnd_iff, Nat.beq_eq] at this
    exact ⟨this.1, by simpa using this.2.1, by simpa using this.2.2.1, this.2.2.2⟩
  · have := allN_spec (allN_spec h2 j hj) x hx
    simp only [bAnd_iff, Nat.beq_eq] at this
    exact ⟨this.1, by simpa using this.2.1, by simpa using this.2.2.1, this.2.2.2⟩
  · have := allN_spec h3 x hx
    simp only [bAnd_iff, Nat.beq_eq] at this
    exact ⟨by simpa using this.1, by simpa using this.2.1, this.2.2⟩
  · have := allN_spec h4 i hi
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, allN_spec this.2.2.1, allN_spec this.2.2.2⟩

theorem t32_sound : enumBFS 32 Data.T32Chain.generators 600 = penumRec 32 6 T32E.cnt T32E.T T32E.PL ∧
    enumOK 32 Data.T32Chain.generators (penumRec 32 6 T32E.cnt T32E.T T32E.PL) = true :=
  penumK_left_sound (cap := 600) szOK32 (gensOK_of t32_gens) t32_hd (fun _ hi => t32_pt hi)

theorem t_sel_parts : (List.range 512).filter qT = ON5.tSel ∧
    T32E.T (List.getD ON5.tSel 0 0) = pidn 32 6 ∧
    Data.T32z = unpack 32 6 (T32E.T (List.getD ON5.tSel 1 0)) ∧ ON5.tSel = [List.getD ON5.tSel 0 0,
      List.getD ON5.tSel 1 0] := by
  have h := t_sel
  unfold tSelOK at h
  simp only [bAnd_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨sel_spec h1, h2, unpack_eq_of_bindArrK h3, ?_⟩
  match hl : ON5.tSel, h4 with
  | [a, b], _ => rfl

theorem t32_part : Data.T32Chain.generators.all (fun g => g.size == 32) = true ∧
    pisInv 32 Data.T32z (pinvCand 32 Data.T32z) = true ∧ Data.T32z.size = 32 ∧
    enumOK 32 Data.T32Chain.generators t32Enum = true ∧ t32Enum.tabs.size = 512 ∧
    (t32Enum.tabs.filter fun x => Data.T32Chain.generators.all fun g =>
      comp 32 x g == comp 32 g x).toList = [idTab 32, Data.T32z] := by
  obtain ⟨s1, s2, s3, s4⟩ := t_sel_parts
  refine ⟨by rw [← Array.all_toList]; quickRfl,
    pisInv_of (f := fun x => Data.T32z[x]!) (fi := zI) rfl (fun _ _ => rfl)
      fun x hx => ⟨(small_parts.2.2.1 x hx).1, (small_parts.2.2.1 x hx).2.2⟩, rfl, ?_, ?_, ?_⟩
  · rw [t32Enum_eq]
    exact t32_sound.2
  · rw [t32Enum_eq]
    simp [penumRec]
    rfl
  · rw [t32Enum_eq]
    simp only [penumRec]
    rw [filter_ofFn (m := T32E.cnt) (f := fun i => unpack 32 6 (T32E.T i))]
    have e : ((List.range 512).filter fun i => Data.T32Chain.generators.all fun g =>
        comp 32 (unpack 32 6 (T32E.T i)) g == comp 32 g (unpack 32 6 (T32E.T i))) = ON5.tSel := by
      rw [← s1]
      apply List.filter_congr
      intro i hi
      have hi' : i < 512 := List.mem_range.1 hi
      rw [all_comm (gensOK_of t32_gens) (penumPt_canon (t32_pt hi'))]
      unfold qT
      rw [strictB_app']
      rfl
    have hcnt : T32E.cnt = 512 := rfl
    rw [hcnt, e, s4]
    simp only [List.map_cons, List.map_nil]
    rw [s2, ← s3, ← idTab_eq]

theorem szOK120 : szOK 120 7 = true := by quickRfl

theorem m_pt {i : Nat} (hi : i < ON5M.cnt) : penumPtK 120 7 (mask 7) (120 * 7) false ON5M.G
    ON5M.GI ON5M.k ON5M.cnt ON5M.T ON5M.PL ON5M.POS ON5M.SRT ON5M.SRI i = true := by
  have e : ON5M.cnt = 40320 := rfl
  have hs : i / 2016 < 20 := by omega
  exact penumSl_spec (mSlAll (i / 2016) hs) i (by simp only [Nat.mul_eq]; omega)
    (by simp only [Nat.mul_eq]; omega) hi

theorem m120_sound : enumBFS 120 Data.M120Chain.generators 50000 =
      penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL ∧
    enumOK 120 Data.M120Chain.generators (penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL) = true :=
  penumK_left_sound (cap := 50000) szOK120 (gensOK_of m_gens) m_hd (fun _ hi => m_pt hi)

theorem blocks_eq (q : Nat → Bool) (b : Nat) (S : Nat → List Nat) :
    ∀ k, (∀ s < k, (List.range' (b * s) b).filter q = S s) →
      (List.range (b * k)).filter q = (List.range k).flatMap S
  | 0, _ => by simp
  | k + 1, h => by
    rw [Nat.mul_succ, List.range_add, List.filter_append,
      blocks_eq q b S k (fun s hs => h s (by omega)), List.range_succ, List.flatMap_append,
      List.flatMap_singleton, ← h k (by omega), List.range'_eq_map_range]

theorem m120_part : Data.M120Chain.generators.all (fun g => g.size == 120) = true ∧
    Data.D120Generators.all (fun g => g.size == 120) = true ∧
    Data.D120Generators.size = 4 ∧
    allBelowN 4 (fun j => pisInv 120 Data.D120Generators[j]!
      (pinvCand 120 Data.D120Generators[j]!)) = true ∧
    enumOK 120 Data.M120Chain.generators m120Enum = true ∧ m120Enum.tabs.size = 40320 ∧
    (m120Enum.tabs.filter fun x => Data.D120Generators.all fun g =>
      comp 120 x g == comp 120 g x).size = 2 ∧
    allBelowN 4 (fun j => memFull 120
      (cLevels 120 Data.M120Chain.base (allSteps Data.M120Chain.strongGenerators
        (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base))
      (allInvSteps Data.M120Chain.strongGenerators
        (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base)
      Data.M120Chain.base Data.D120Generators[j]!) = true := by
  obtain ⟨hD, hS, -, hlev, hsift⟩ := small_parts
  have me : m120Enum = penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL := m120_sound.1
  refine ⟨by rw [← Array.all_toList]; quickRfl, by rw [← Array.all_toList]; quickRfl, rfl,
    allBelowN_iff.2 fun j hj => pisInv_of (f := dF j) (fi := dFI j)
      (by have hj' : j < 4 := hj; interval_cases j <;> rfl)
      (fun x hx => (hD j hj x hx).1.symm) fun x hx => ⟨(hD j hj x hx).2.1, (hD j hj x hx).2.2.2⟩,
    by rw [me]; exact m120_sound.2, by rw [me]; simp [penumRec]; rfl, ?_,
    allBelowN_iff.2 fun j hj => ?_⟩
  · rw [me]
    simp only [penumRec]
    rw [filter_ofFn (m := ON5M.cnt) (f := fun i => unpack 120 7 (ON5M.T i)), List.size_toArray,
      List.length_map]
    have hcnt : ON5M.cnt = 2016 * 20 := rfl
    have e : ((List.range ON5M.cnt).filter fun i => Data.D120Generators.all fun g =>
        comp 120 (unpack 120 7 (ON5M.T i)) g == comp 120 g (unpack 120 7 (ON5M.T i))) =
        (List.range ON5M.cnt).filter qD := by
      apply List.filter_congr
      intro i hi
      have hi' : i < ON5M.cnt := List.mem_range.1 hi
      rw [all_comm (gensOK_of d_gens) (penumPt_canon (m_pt hi'))]
      unfold qD
      rw [strictB_app']
    rw [e, hcnt, blocks_eq qD 2016 selIn 20 fun s hs => by
      have h := selFrom_spec qD 2016 _ _ (dSelAll s hs)
      have e2 : Nat.mul s 2016 = 2016 * s := Nat.mul_comm s 2016
      rw [e2] at h
      exact h]
    have hd : ((List.range 20).flatMap selIn).length = 2 := by decide +kernel
    exact hd
  · exact memFull3_sound (n := 120) (F := sF) (FI := sFI) (B := sB) (G := dF j) (IDX := sIDX)
      (LEN := sLEN) (Mr := sMr) (PTS := sPTS) (POS := sPOS) (PAR := sPAR) (LAB := sLAB) rfl
      (fun j' hj' x hx => ⟨(hS j' hj' x hx).1.symm, (hS j' hj' x hx).2⟩) rfl
      (fun k hk => ⟨rfl, by interval_cases k <;> decide⟩) (fun y hy => (hD j hj y hy).1.symm)
      (fun y hy => (hD j hj y hy).2.1)
      (fun i hi => (hlev i hi).1) (fun i hi => (hlev i hi).2.1) (fun i hi => (hlev i hi).2.2.1)
      (fun i hi => (hlev i hi).2.2.2) (hsift j hj)

theorem psl_part : fixedSet 120 ((levIdx Data.PSL120Chain.strongGenerators Data.PSL120Chain.base 1).map
    fun j => Data.PSL120Chain.strongGenerators[j]!).toArray = [0] := by
  unfold fixedSet levIdx pfixes
  simp only [allBelowN_eq, ← Array.all_toList]
  decide +kernel

theorem fano_part : Data.targetFanoBlocks.size = 120 ∧
    allBelowN 120 (fun i => Data.targetFanoBlocks[i]!.size == 7 &&
      sortedOK Data.targetFanoBlocks[i]! &&
      Data.targetFanoBlocks[i]!.all (fun x => decide (x < 21))) = true ∧
    allBelowN 120 (fun i => allBelowN 120 fun k => i == k ||
      Data.targetFanoBlocks[i]!.toList != Data.targetFanoBlocks[k]!.toList) = true ∧
    Data.PSL120Chain.generators.size = 12 ∧ Data.PSL21Chain.generators.size = 12 ∧
    allBelowN 12 (fun j => allBelowN 120 fun i =>
      decide ((Data.PSL120Chain.generators[j]!)[i]! < 120) &&
        sortedImage Data.PSL21Chain.generators[j]! Data.targetFanoBlocks[i]! ==
          Data.targetFanoBlocks[(Data.PSL120Chain.generators[j]!)[i]!]!.toList) = true := by
  simp only [sortedOK, allBelowN_eq, ← Array.all_toList]
  decide +kernel

open Certificates in
open CFSG CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native in
theorem facts2216 : (Data.T32Chain.generators.all (fun g => g.size == 32) = true ∧
      pisInv 32 Data.T32z (pinvCand 32 Data.T32z) = true ∧ Data.T32z.size = 32 ∧
      enumOK 32 Data.T32Chain.generators t32Enum = true ∧ t32Enum.tabs.size = 512 ∧
      (t32Enum.tabs.filter fun x => Data.T32Chain.generators.all fun g =>
        comp 32 x g == comp 32 g x).toList = [idTab 32, Data.T32z]
    )
    ∧ (Data.M120Chain.generators.all (fun g => g.size == 120) = true ∧
      Data.D120Generators.all (fun g => g.size == 120) = true ∧
      Data.D120Generators.size = 4 ∧
      allBelowN 4 (fun j => pisInv 120 Data.D120Generators[j]!
        (pinvCand 120 Data.D120Generators[j]!)) = true ∧
      enumOK 120 Data.M120Chain.generators m120Enum = true ∧ m120Enum.tabs.size = 40320 ∧
      (m120Enum.tabs.filter fun x => Data.D120Generators.all fun g =>
        comp 120 x g == comp 120 g x).size = 2 ∧
      allBelowN 4 (fun j => memFull 120
        (cLevels 120 Data.M120Chain.base (allSteps Data.M120Chain.strongGenerators
          (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base))
        (allInvSteps Data.M120Chain.strongGenerators
          (pinvs 120 Data.M120Chain.strongGenerators) Data.M120Chain.base)
        Data.M120Chain.base Data.D120Generators[j]!) = true
    )
    ∧ (fixedSet 120 ((levIdx Data.PSL120Chain.strongGenerators Data.PSL120Chain.base 1).map
      fun j => Data.PSL120Chain.strongGenerators[j]!).toArray = [0]
    )
    ∧ (Data.targetFanoBlocks.size = 120 ∧
      allBelowN 120 (fun i => Data.targetFanoBlocks[i]!.size == 7 &&
        sortedOK Data.targetFanoBlocks[i]! &&
        Data.targetFanoBlocks[i]!.all (fun x => decide (x < 21))) = true ∧
      allBelowN 120 (fun i => allBelowN 120 fun k => i == k ||
        Data.targetFanoBlocks[i]!.toList != Data.targetFanoBlocks[k]!.toList) = true ∧
      Data.PSL120Chain.generators.size = 12 ∧ Data.PSL21Chain.generators.size = 12 ∧
      allBelowN 12 (fun j => allBelowN 120 fun i =>
        decide ((Data.PSL120Chain.generators[j]!)[i]! < 120) &&
          sortedImage Data.PSL21Chain.generators[j]! Data.targetFanoBlocks[i]! ==
            Data.targetFanoBlocks[(Data.PSL120Chain.generators[j]!)[i]!]!.toList) = true
    ) := ⟨t32_part, m120_part, psl_part, fano_part⟩

end CertificateChecks.KernelSpor.ON5K

end

module

public import Certificates.Kernel.SporSch.Tits.Prim2269M0
public import Certificates.Kernel.SporSch.Tits.Prim2269M1
public import Certificates.Kernel.SporSch.Tits.Prim2269M2
public import Certificates.Kernel.SporSch.Tits.Prim2269M3
public import Certificates.Kernel.SporSch.Tits.Prim2269M4
public import Certificates.Kernel.SporSch.Tits.Prim2269M5
public import Certificates.Kernel.SporSch.Tits.Prim2269M6
public import Certificates.Kernel.SporSch.Tits.Prim2269M7
public import Certificates.Kernel.SporSch.Tits.Prim2269M8
public import Certificates.Kernel.SporSch.Tits.Stab2270
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.MergeG
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Certificates
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelMisc
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsCommon
open CertificateChecks.KernelSporSch.TitsStab

theorem toArray_map_get {f : Nat → Array Nat} {m i : Nat} (hi : i < m) :
    ((List.range m).map f).toArray[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem toArray_map_get' {f : List Int → Array Nat} {L : List (List Int)} {i : Nat}
    (hi : i < L.length) : (L.map f).toArray[i]! = f L[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos L i hi]
  simp

theorem h0_eq : titsH0Idx = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by
  unfold titsH0Idx
  rw [← kH0]
  refine List.filter_congr fun j hj => ?_
  rw [der_eq (List.mem_range.1 hj), unpack_get (by norm_num), nat_beq]

theorem h0_range : [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] = (List.range 11).map (· + 2) := rfl

theorem hGens : titsH0Arrs.size = 11 ∧
    ∀ i < 11, titsH0Arrs[i]! = unpack 1755 11 (TitsD.S (Nat.add i 2)) := by
  unfold titsH0Arrs
  rw [h0_eq, h0_range, List.map_map]
  refine ⟨by simp, fun i hi => ?_⟩
  rw [toArray_map_get hi, Function.comp_apply]
  exact der_eq (by omega)

theorem nW_len : titsNWords.length = 4 := rfl

theorem nGens : titsNStarArrs.size = 4 ∧ ∀ i < 4, titsNStarArrs[i]! = unpack 2925 12 (TitsNW.W i) := by
  unfold titsNStarArrs
  refine ⟨by simp [nW_len], fun i hi => ?_⟩
  rw [toArray_map_get' (by rw [nW_len]; exact hi)]
  have hS : titsTStarArrs.size = 13 ∧ ∀ j < 13, titsTStarArrs[j]! = unpack 2925 12 (TitsSS.T j) :=
    ⟨tS_size, fun _ hj => tS_get hj⟩
  match i, hi with
  | 0, _ => exact wordW_sound hw12 hS aTp' nW0
  | 1, _ => exact wordW_sound hw12 hS aTp' nW1
  | 2, _ => exact wordW_sound hw12 hS aTp' nW2
  | 3, _ => exact wordW_sound hw12 hS aTp' nW3

theorem gen_size : titsGenArrs.size = 4 := by
  unfold titsGenArrs titsField1755
  simp

theorem dG' : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (TitsText.F j) (TitsSD.GI j)) =
    true := by
  simpa only [permW_eq] using dG

theorem wD {wd : List Int} {r : Nat} (h : wordW 1755 11 TitsText.F TitsSD.GI 4 wd r = true) :
    wordArr 1755 titsGenArrs wd = unpack 1755 11 r :=
  wordW_sound hw11 ⟨gen_size, fun _ hi => gen_eq hi⟩ dG' h

theorem dD_size : titsDArrs.size = 2 := by
  unfold titsDArrs
  simp

theorem uD : ∀ {j : Nat}, j < 2 →
    wordArr 1755 titsGenArrs (titsU j) = unpack 1755 11 (TitsSD.U j)
  | 0, _ => wD dU0u
  | 1, _ => wD dU1u

theorem vD : ∀ {j : Nat}, j < 2 →
    wordArr 1755 titsGenArrs (titsV j) = unpack 1755 11 (TitsSD.V j)
  | 0, _ => wD dU0v
  | 1, _ => wD dU1v

theorem dD_get {j : Nat} (hj : j < 2) : titsDArrs[j]! = unpack 1755 11 (TitsSD.T j) := by
  unfold titsDArrs
  rw [getElem!_ofFn_of_lt _ hj]
  dsimp only
  unfold titsDArr commArr
  have hu := uD hj
  have hv := vD hj
  obtain ⟨pu, pv⟩ := (bAnd_iff _ _).1 (allN_spec dUp j hj)
  obtain ⟨c1, c23⟩ := (bAnd_iff _ _).1 (allN_spec dC j hj)
  obtain ⟨c2, c3⟩ := (bAnd_iff _ _).1 c23
  rw [hu, hv, inv_unpack pu, inv_unpack pv, eq2W_sound c1, eq2W_sound c2, eq2W_sound c3]

theorem repsH_bind : (#[0, 1, 6, 24, 87] : Array Nat).size = 5 ∧
    ∀ c < 5, (#[0, 1, 6, 24, 87] : Array Nat)[c]! = pg 11 (mask 11) TitsFH.REP c :=
  ⟨rfl, fun _ hc => by rw [rHe, unpackW_get hc]⟩

theorem repsN_bind : (#[0, 1, 7, 27, 107, 141] : Array Nat).size = 6 ∧
    ∀ c < 6, (#[0, 1, 7, 27, 107, 141] : Array Nat)[c]! = pg 12 (mask 12) TitsFN.REP c :=
  ⟨rfl, fun _ hc => by rw [rNe, unpackW_get hc]⟩

theorem forH : titsH0Forest = (unpack 1755 11 TitsFH.LAB, unpack 1755 11 TitsFH.DEP,
    unpack 1755 11 TitsFH.PAR, unpack 1755 11 TitsFH.GL) := by
  unfold titsH0Forest
  exact bfsTK_sound hw11 hGens hCan repsH_bind fH

theorem forN : titsNForest = (unpack 2925 12 TitsFN.LAB, unpack 2925 12 TitsFN.DEP,
    unpack 2925 12 TitsFN.PAR, unpack 2925 12 TitsFN.GL) := by
  unfold titsNForest
  exact bfsTK_sound hw12 nGens nCan repsN_bind fN

theorem repLe {n w REP LAB : Nat} {reps : Array Nat} (m : Nat)
    (he : reps = unpack m w REP) (h0 : Nat.beq (Nat.shiftRight REP (m * w)) 0 = true)
    (h : allN n (fun x => Nat.ble (pgW w REP (pgW w LAB x)) x) = true) :
    allLt n (fun x => decide (reps[(unpack n w LAB)[x]!]! ≤ x)) = true := by
  rw [allLt_iff]
  intro x hx
  have hk := allN_spec h x hx
  rw [pgW_eq, pgW_eq, Nat.ble_eq] at hk
  rw [unpackW_get hx, he, unpackW_get0 h0]
  exact decide_eq_true hk

theorem bytes_eq : titsMergesBytes = titsMergesText.toUTF8 := rfl

theorem dig_eq {o : Nat} (ho : o < 623 * 243) : hexAt titsMergesBytes o 1 = digK TitsMg.F o := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound kMg (o / 623) (by omega)
  rw [← TitsMg.eq] at h
  have hm : o % 623 < 623 := Nat.mod_lt _ (by norm_num)
  have h1 : (hexTable 1 623 (623 * (o / 623)) titsMergesText)[o % 623]! =
      hexAt titsMergesBytes o 1 := by
    unfold hexTable
    rw [getElem!_ofFn_of_lt _ hm, bytes_eq]
    dsimp only
    rw [Nat.one_mul, Nat.div_add_mod]
  rw [← h1, h, unpackW_get hm]
  rfl

theorem mergeAt_eq {k : Nat} (hk : 7 * k + 7 ≤ 623 * 243) :
    titsMergeAt k = (digK TitsMg.F (7 * k), hex3K TitsMg.F (7 * k + 1),
      hex3K TitsMg.F (7 * k + 4)) := by
  unfold titsMergeAt
  rw [dig_eq (by omega), hexAt_three, hexAt_three, dig_eq (by omega), dig_eq (by omega),
    dig_eq (by omega), dig_eq (by omega), dig_eq (by omega), dig_eq (by omega)]
  rfl

theorem mvO {l : Nat} (hl : l < 4) : mergeVals (titsOrigMerge l) = (List.range 1753).map
    fun k => (recI (1753 * l) k, recU 1755 (1753 * l) k, recV 1755 (1753 * l) k) := by
  unfold mergeVals titsOrigMerge titsOrigMergeVals
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply, finPt]
  rw [mergeAt_eq (by omega)]
  rfl

theorem mvS {l : Nat} (hl : l < 5) : mergeVals (titsOtherMerge l) = (List.range 2923).map
    fun k => (recI (4 * 1753 + 2923 * l) k, recU 2925 (4 * 1753 + 2923 * l) k,
      recV 2925 (4 * 1753 + 2923 * l) k) := by
  unfold mergeVals titsOtherMerge titsOtherMergeVals
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply, finPt]
  rw [mergeAt_eq (by omega)]
  rfl

theorem gD : titsDArrs.size = 2 ∧ ∀ i < 2, titsDArrs[i]! = unpack 1755 11 (TitsSD.T i) :=
  ⟨dD_size, fun _ hi => dD_get hi⟩

theorem gS : titsDStarArrs.size = 2 ∧ ∀ i < 2, titsDStarArrs[i]! = unpack 2925 12 (TitsSS.T i) :=
  ⟨dS_size, fun _ hi => dS_get hi⟩

theorem labH : orbitLabelOK 1755 titsH0Arrs 5 titsH0Forest.1 #[0, 1, 6, 24, 87] titsH0Forest.2.1
    titsH0Forest.2.2.1 titsH0Forest.2.2.2 = true := by
  rw [forH]
  exact labOKK_sound hw11 hGens hCan repsH_bind lH

theorem labN : orbitLabelOK 2925 titsNStarArrs 6 titsNForest.1 #[0, 1, 7, 27, 107, 141]
    titsNForest.2.1 titsNForest.2.2.1 titsNForest.2.2.2 = true := by
  have h := labOKK_sound hw12 nGens nCan repsN_bind lN
  rw [forN]
  exact h

theorem cntH : (List.range 5).map (labelCount 1755 titsH0Forest.1) = titsStabSizes := by
  rw [forH]
  exact (congrArg (List.map · (List.range 5)) (funext (cntK_sound 1755 11 TitsFH.LAB))).trans cH

theorem cntN : (List.range 6).map (labelCount 2925 titsNForest.1) = titsOtherSizes := by
  rw [forN]
  exact (congrArg (List.map · (List.range 6)) (funext (cntK_sound 2925 12 TitsFN.LAB))).trans cN

theorem leH : allLt 1755 (fun x => decide ((#[0, 1, 6, 24, 87] : Array ℕ)[titsH0Forest.1[x]!]! ≤ x)) =
    true := by
  rw [forH]
  exact repLe 5 rHe rH0 rH

theorem leN : allLt 2925
    (fun x => decide ((#[0, 1, 7, 27, 107, 141] : Array ℕ)[titsNForest.1[x]!]! ≤ x)) = true := by
  rw [forN]
  exact repLe 6 rNe rN0 rN

theorem mergeO : ∀ {l : Nat}, l < 4 →
    mergeOK 1755 titsDArrs 0 titsStabReps[l]! (mergeVals (titsOrigMerge l)) = true
  | 0, hl => by rw [mvO hl]; exact mergeCKG_sound hw11 gD dCan rfl mO0
  | 1, hl => by rw [mvO hl]; exact mergeCKG_sound hw11 gD dCan rfl mO1
  | 2, hl => by rw [mvO hl]; exact mergeCKG_sound hw11 gD dCan rfl mO2
  | 3, hl => by rw [mvO hl]; exact mergeCKG_sound hw11 gD dCan rfl mO3

theorem mergeS : ∀ {l : Nat}, l < 5 →
    mergeOK 2925 titsDStarArrs 0 titsOtherReps[l + 1]! (mergeVals (titsOtherMerge l)) = true
  | 0, hl => by rw [mvS hl]; exact mergeCKG_sound hw12 gS sCan rfl mS0
  | 1, hl => by rw [mvS hl]; exact mergeCKG_sound hw12 gS sCan rfl mS1
  | 2, hl => by rw [mvS hl]; exact mergeCKG_sound hw12 gS sCan rfl mS2
  | 3, hl => by rw [mvS hl]; exact mergeCKG_sound hw12 gS sCan rfl mS3
  | 4, hl => by rw [mvS hl]; exact mergeCKG_sound hw12 gS sCan rfl mS4

theorem facts : titsH0Idx = [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] ∧
    titsStabReps = [1, 6, 24, 87] ∧ titsStabSizes = [1, 10, 80, 640, 1024] ∧
    orbitLabelOK 1755 titsH0Arrs 5 titsH0Forest.1 #[0, 1, 6, 24, 87] titsH0Forest.2.1
      titsH0Forest.2.2.1 titsH0Forest.2.2.2 = true ∧
    (List.range 5).map (labelCount 1755 titsH0Forest.1) = titsStabSizes ∧
    allLt 1755 (fun x => decide ((#[0, 1, 6, 24, 87] : Array ℕ)[titsH0Forest.1[x]!]! ≤ x)) =
      true ∧
    (∀ l < 4, (titsOrigMerge l).length = 1753 ∧
      mergeOK 1755 titsDArrs 0 titsStabReps[l]! (mergeVals (titsOrigMerge l)) = true) ∧
    titsOtherReps = [0, 1, 7, 27, 107, 141] ∧ titsOtherSizes = [1, 12, 96, 768, 1024, 1024] ∧
    orbitLabelOK 2925 titsNStarArrs 6 titsNForest.1 #[0, 1, 7, 27, 107, 141] titsNForest.2.1
      titsNForest.2.2.1 titsNForest.2.2.2 = true ∧
    (List.range 6).map (labelCount 2925 titsNForest.1) = titsOtherSizes ∧
    allLt 2925 (fun x => decide ((#[0, 1, 7, 27, 107, 141] : Array ℕ)[titsNForest.1[x]!]! ≤ x)) =
      true ∧
    (∀ l < 5, (titsOtherMerge l).length = 2923 ∧
      mergeOK 2925 titsDStarArrs 0 titsOtherReps[l + 1]! (mergeVals (titsOtherMerge l)) =
        true) :=
  ⟨h0_eq, rfl, rfl, labH, cntH, leH,
    fun _ hl => ⟨by simp [titsOrigMerge, titsOrigMergeVals], mergeO hl⟩, rfl, rfl, labN, cntN,
    leN, fun _ hl => ⟨by simp [titsOtherMerge, titsOtherMergeVals], mergeS hl⟩⟩

end CertificateChecks.KernelSporSch.TitsPrim

end

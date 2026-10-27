module

public import Certificates.Kernel.LocalQT.Tits4139.K
public import Certificates.Kernel.SporSch.Tits.Stab2270
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLocalQT.Tits4139

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Certificates CFSG.QuasithinUnique.Setup.X6.TitsLat
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsStab
open CertificateChecks.KernelLocalQT

theorem toArray_map_get {f : List Int → Array Nat} {L : List (List Int)} {i : Nat}
    (hi : i < L.length) : (L.map f).toArray[i]! = f L[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos L i hi]
  simp

theorem sW_len : titsSWords.length = 3 := rfl

theorem sGens : titsSFlagArrs.size = 3 ∧
    ∀ i < 3, titsSFlagArrs[i]! = unpack 8775 14 (TitsSW.W i) := by
  unfold titsSFlagArrs
  refine ⟨by simp [sW_len], fun i hi => ?_⟩
  rw [toArray_map_get (by rw [sW_len]; exact hi)]
  have hS : titsTFlagArrs.size = 13 ∧ ∀ j < 13, titsTFlagArrs[j]! = unpack 8775 14 (TitsSF.T j) :=
    ⟨tF_size, fun _ hj => tF_get hj⟩
  match i, hi with
  | 0, _ => exact wordW_sound hw14 hS fTp' sW0
  | 1, _ => exact wordW_sound hw14 hS fTp' sW1
  | 2, _ => exact wordW_sound hw14 hS fTp' sW2

theorem repsS_bind : titsSFlagReps.size = 18 ∧
    ∀ c < 18, titsSFlagReps[c]! = pg 14 (mask 14) TitsFS.REP c :=
  ⟨rfl, fun _ hc => by rw [rSe, unpackW_get hc]⟩

theorem forS : titsSFlagForest = (unpack 8775 14 TitsFS.LAB, unpack 8775 14 TitsFS.DEP,
    unpack 8775 14 TitsFS.PAR, unpack 8775 14 TitsFS.GL) := by
  unfold titsSFlagForest
  exact bfsTK_sound hw14 sGens sCan repsS_bind fS

theorem labS : orbitLabelOK 8775 titsSFlagArrs 18 titsSFlagForest.1 titsSFlagReps
    titsSFlagForest.2.1 titsSFlagForest.2.2.1 titsSFlagForest.2.2.2 = true := by
  rw [forS]
  dsimp only
  exact labOKK_sound hw14 sGens sCan repsS_bind lS

theorem cntS : (List.range 18).map (labelCount 8775 titsSFlagForest.1) = titsSFlagSizes := by
  rw [forS]
  dsimp only
  exact (congrArg (List.map · (List.range 18)) (funext (cntK_sound 8775 14 TitsFS.LAB))).trans cS

theorem beqB_eq (a b : Bool) : beqB a b = (a == b) := by
  cases a <;> cases b <;> rfl

theorem labSet {c : Nat} {L : List Nat} {p : Nat → Bool} (hp : ∀ x, p x = L.contains x)
    (h : allN 8775 (fun x => beqB (Nat.beq (pgW 14 TitsFS.LAB x) c) (memN x L)) = true) :
    allLt 8775 (fun x => ((unpack 8775 14 TitsFS.LAB)[x]! == c) == p x) = true := by
  rw [allLt_iff]
  intro x hx
  have hk := allN_spec h x hx
  rw [beqB_eq, memN_contains, pgW_eq, ← hp] at hk
  rw [unpackW_get hx, nat_beq]
  exact hk

theorem lab0 : allLt 8775 (fun x => (titsSFlagForest.1[x]! == 0) == (x == 0)) = true := by
  rw [forS]
  dsimp only
  exact labSet (fun x => by rw [Bool.eq_iff_iff]; simp) s0

theorem lab1 : allLt 8775 (fun x => (titsSFlagForest.1[x]! == 1) == (x == 1 || x == 3)) = true := by
  rw [forS]
  dsimp only
  exact labSet (fun x => by rw [Bool.eq_iff_iff]; simp) s1

theorem lab2 : allLt 8775
    (fun x => (titsSFlagForest.1[x]! == 2) == (x == 2 || x == 5 || x == 10 || x == 20)) = true := by
  rw [forS]
  dsimp only
  exact labSet (fun x => by rw [Bool.eq_iff_iff]; simp [or_assoc]) s2

theorem ptFacts : ∀ l < 15, lettersOK 13 (titsFlagRepWord l) = true ∧
    lettersOK 13 (titsFlagZWord l) = true ∧
    (wordArr 8775 titsTFlagArrs (titsFlagRepWord l))[0]! = titsFlagMergeReps.getD l 0 ∧
    (wordArr 8775 titsTFlagArrs (titsFlagZWord l))[0]! ∈ [2, 5, 10, 20] := by
  intro l hl
  obtain ⟨h1, r1⟩ := (bAnd_iff _ _).1 (allN_spec pts l hl)
  obtain ⟨h2, r2⟩ := (bAnd_iff _ _).1 r1
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 r2
  refine ⟨lettersK_sound h1, lettersK_sound h2, ?_, ?_⟩
  · rw [ptF h1 (by norm_num)]
    exact Nat.eq_of_beq_eq_true h3
  · rw [ptF h2 (by norm_num)]
    exact memN_spec h4

theorem facts : orbitLabelOK 8775 titsSFlagArrs 18 titsSFlagForest.1 titsSFlagReps
      titsSFlagForest.2.1 titsSFlagForest.2.2.1 titsSFlagForest.2.2.2 = true ∧
    (List.range 18).map (labelCount 8775 titsSFlagForest.1) = titsSFlagSizes ∧
    allLt 8775 (fun x => (titsSFlagForest.1[x]! == 0) == (x == 0)) = true ∧
    allLt 8775 (fun x => (titsSFlagForest.1[x]! == 1) == (x == 1 || x == 3)) = true ∧
    allLt 8775 (fun x => (titsSFlagForest.1[x]! == 2) == (x == 2 || x == 5 || x == 10 || x == 20)) =
      true ∧
    (∀ l < 15, lettersOK 13 (titsFlagRepWord l) = true ∧ lettersOK 13 (titsFlagZWord l) = true ∧
      (wordArr 8775 titsTFlagArrs (titsFlagRepWord l))[0]! = titsFlagMergeReps.getD l 0 ∧
      (wordArr 8775 titsTFlagArrs (titsFlagZWord l))[0]! ∈ [2, 5, 10, 20]) :=
  ⟨labS, cntS, lab0, lab1, lab2, ptFacts⟩

end CertificateChecks.KernelLocalQT.Tits4139

end

module

public import Certificates.Kernel.SporSch.Co3.Joint
public import Certificates.Kernel.SporSch.Co3.Second
public import Certificates.Kernel.Sporadic.M12Alt.Check
public import CFSG.Certificates.Kernel.SporSch.MCountCSound
public import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
meta import CFSG.Sporadic.Schreier.Co3GenerationCheckInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.M11Data

public section

set_option maxRecDepth 400000

#kss_perms CertificateChecks.KernelSporSch.Co3KD 4 CFSG.Sporadic.Schreier.Co3.co3D0Kappa1

namespace CertificateChecks.KernelSporSch.Co3Gen

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.M11 CFSG.KS.MEnum
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.Co3Second (ITP C12 it_bind c12_line)

@[expose] noncomputable def D0 (k : Nat) : Nat := Co3Text.L (Nat.add 30 k)

@[expose] noncomputable def GMM (i : Nat) : Nat := nIf(Nat.blt i 7, Co3M.S i, Co3M1.S (Nat.sub i 7))

theorem d0_lines : allN 5 (fun j => Nat.beq (D0 j) (Co3Text.L (Nat.add 30 j))) = true := by quickRfl

theorem d0_sifts : allN 5 (fun k => bAnd(Co3M.sift (D0 k), bAnd(Co3Text.hiOK (D0 k),
    siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3M1.LR Co3M1.TRI Co3M1.BP 4 0 (D0 k)))) = true := by
  quickRfl

theorem d0_range : allN 5 (fun k => allN 276 (fun i => Nat.blt (pg 9 (mask 9) (D0 k) i) 276)) =
    true := by
  quickRfl

theorem covers_ok : coversK 276 9 GMM 13 Co3J.S 13 = true := by quickRfl

theorem kappa_ok : allN 5 (fun k => kappaK 276 9 12 4 ITP C12 (pinvS 12 4 (mask 4) C12) (D0 k)
    (Co3KD k)) = true := by quickRfl

theorem kd_canon : allN 5 (fun k => canonK 12 4 (mask 4) (12 * 4) (Co3KD k)) = true := by quickRfl

theorem s0 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 0 Co3KD 5) 2 =
    true := by quickRfl
theorem s1 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 1 Co3KD 5) 0 =
    true := by quickRfl
theorem s2 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 2 Co3KD 5) 0 =
    true := by quickRfl
theorem s3 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 3 Co3KD 5) 0 =
    true := by quickRfl
theorem s4 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 4 Co3KD 5) 0 =
    true := by quickRfl
theorem s5 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 5 Co3KD 5) 0 =
    true := by quickRfl
theorem s6 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 6 Co3KD 5) 0 =
    true := by quickRfl
theorem s7 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 7 Co3KD 5) 0 =
    true := by quickRfl
theorem s8 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 8 Co3KD 5) 0 =
    true := by quickRfl
theorem s9 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 9 Co3KD 5) 0 =
    true := by quickRfl
theorem s10 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 10 Co3KD 5) 0 =
    true := by quickRfl
theorem s11 : Nat.beq (mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 11 Co3KD 5) 0 =
    true := by quickRfl

@[expose] def CS : List Nat := [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem hc : ∀ i < 12, mCntC 12 4 [0, 1, 2, 3, 4] 12 M12Alt.tA M12Alt.tB M12Alt.W 1 i Co3KD 5 =
    CS.getD i 0 := by
  intro i hi
  interval_cases i
  · exact Nat.eq_of_beq_eq_true s0
  · exact Nat.eq_of_beq_eq_true s1
  · exact Nat.eq_of_beq_eq_true s2
  · exact Nat.eq_of_beq_eq_true s3
  · exact Nat.eq_of_beq_eq_true s4
  · exact Nat.eq_of_beq_eq_true s5
  · exact Nat.eq_of_beq_eq_true s6
  · exact Nat.eq_of_beq_eq_true s7
  · exact Nat.eq_of_beq_eq_true s8
  · exact Nat.eq_of_beq_eq_true s9
  · exact Nat.eq_of_beq_eq_true s10
  · exact Nat.eq_of_beq_eq_true s11

theorem d0_eq (k : Nat) (hk : k < 5) : co3D0Arrs[k]! = unpack 276 9 (D0 k) :=
  (Co3Text.field_of (f := 4) rfl (by omega) d0_lines).2 k hk

theorem kd_eq (k : Nat) (hk : k < 5) : co3D0Kappa1[k]! = unpack 12 4 (Co3KD k) := by
  have hc : co3C12Arr = unpack 12 4 C12 :=
    (Co3Text12.field_of (f := 1) (F := fun _ => C12) rfl (by omega) c12_line).2 0 (by omega)
  rw [co3D0Kappa1, getElem!_pos _ k (by simp; omega), Array.getElem_ofFn]
  change renameA 12 co3C12Arr (restrictA co3ItArr co3D0Arrs[k]!) = _
  rw [hc, co3ItArr, toArray_eq_of_bindListK it_bind, d0_eq k hk]
  exact kappaK_sound (allN_spec kappa_ok k hk)

theorem mm1_get (i : Nat) (hi : i < 13) : co3MM1Gens[i]! = unpack 276 9 (GMM i) := by
  have hM : co3MArrs.size = 14 := Co3M.binds.2.2.2.1
  have hM1 : co3M1Arrs.size = 11 := Co3M1.binds.2.2.2.1
  rw [co3MM1Gens, getElem!_pos _ i (by simp [hM, hM1]; omega)]
  rcases Nat.lt_or_ge i 7 with h | h
  · have hb : Nat.blt i 7 = true := Nat.blt_eq.mpr h
    have e : GMM i = Co3M.S i := by
      unfold GMM
      rw [hb]
    rw [e, ← Co3M.arr_eq i (by omega), getElem!_pos co3MArrs i (by omega)]
    simp [hM, h]
  · have hb : Nat.blt i 7 = false :=
      Bool.eq_false_iff.mpr fun h' => absurd (Nat.blt_eq.mp h') (by omega)
    have e : GMM i = Co3M1.S (i - 7) := by
      unfold GMM
      rw [hb]
      rfl
    rw [e, ← Co3M1.arr_eq (i - 7) (by omega), getElem!_pos co3M1Arrs (i - 7) (by omega),
      Array.getElem_append]
    simp [hM, Nat.not_lt.mpr h]

theorem extract_get {S : Array (Array Nat)} {k j : Nat} (hj : j < k) (hk : k ≤ S.size) :
    (S.extract 0 k)[j]! = S[j]! := by
  rw [getElem!_pos (S.extract 0 k) j (by simp; omega), getElem!_pos S j (by omega)]
  simp

theorem count_eq : countProducts 12 co3D0Test (levelTables m12Certificate) (idT 12) = 2 := by
  have h := mCntC_sound (gA := m12gA) (gB := m12gB) (words := m12Words) (hn := by decide)
    (bv := #v[0, 1, 2, 3, 4]) (hbs := by decide) (sub := 1) (K := 5) (D := Co3KD)
    (Ds := co3D0Kappa1) (CS := CS) (by decide) (by decide) (by decide) rfl rfl (by decide)
    M12Alt.base rfl
    ⟨by decide, by decide⟩ ⟨by simp [co3D0Kappa1], kd_eq⟩ (fun j hj => allN_spec kd_canon j hj)
    rfl hc
  have h2 : CS.sum = 2 := rfl
  rw [h2] at h
  unfold co3D0Test co3ToT m12Certificate
  exact h

theorem facts : (rawChainOK 276 (co3JointArrs.extract 0 co3JointGenCount) co3JointArrs
        co3JointBaseArr (wordsArr co3JointGenCount co3JointStrongCount co3JointDerivations) 4 = true ∧
      rawOrbitSizes 276 co3JointArrs co3JointBaseArr = [276, 275, 112, 81, 20, 18, 2])
    ∧ (coversOK 276 co3MM1Gens (co3JointArrs.extract 0 13) = true ∧
      (∀ k < 5, siftA 276 co3MLevels co3MBaseArr 0 co3D0Arrs[k]! = true ∧
        siftA 276 co3M1Levels co3M1BaseArr 0 co3D0Arrs[k]! = true))
    ∧ (countProducts 12 co3D0Test (levelTables m12Certificate) (idT 12) = 2) := by
  refine ⟨⟨rawChainK_sound (NS := 18) (CH := 16) Co3J.binds Co3J.head Co3J.hl (by norm_num)
      Co3J.hs, ?_⟩, ⟨?_, fun k hk => ?_⟩, count_eq⟩
  · rw [rawOrbitSizesK_sound Co3J.binds Co3J.perm Co3J.hl]
    decide
  · refine coversK_sound ⟨?_, mm1_get⟩ ⟨?_, fun j hj => ?_⟩ covers_ok
    · simp [co3MM1Gens, Co3M.binds.2.2.2.1, Co3M1.binds.2.2.2.1]
    · simp [Co3J.binds.2.2.2.1]
    · rw [extract_get hj (by rw [Co3J.binds.2.2.2.1]; omega)]
      exact Co3J.arr_eq j (by omega)
  · obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec d0_sifts k hk)
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    exact ⟨siftK_soundR Co3M.binds Co3M.perm Co3M.hl (d0_eq k hk) (Nat.eq_of_beq_eq_true h3)
        (allN_spec d0_range k hk) h1,
      siftK_soundR Co3M1.binds Co3M1.perm Co3M1.hl (d0_eq k hk) (Nat.eq_of_beq_eq_true h3)
        (allN_spec d0_range k hk) h4⟩

end CertificateChecks.KernelSporSch.Co3Gen

end

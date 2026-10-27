module

public import Certificates.Kernel.SporSch.Co3.Bind12
public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.Co3.M
public import Certificates.Kernel.Sporadic.Co3.Single
public import CFSG.Certificates.Kernel.SporSch.KappaSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Spor.BindList
public import Certificates.Data.Kernel.Spor.M11
public import CFSG.Sporadic.Schreier.Co3SecondCheckInputs
meta import CFSG.Sporadic.Schreier.Co3SecondCheckInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Spor.RawSlSound

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSporSch.Co3M1C 276 9 16
  CFSG.Sporadic.Schreier.Co3.co3M1CommArrs CFSG.Sporadic.Schreier.Co3.co3M1CommBaseArr 3
  CFSG.Sporadic.Schreier.Co3.co3M1CommDerivations

#ks_rawchain CertificateChecks.KernelSporSch.Co3M112 12 4 4
  CFSG.Sporadic.Schreier.Co3.co3M112Arrs CFSG.Sporadic.Schreier.Co3.co3M112BaseArr 5
  CFSG.Sporadic.Schreier.Co3.co3M112Derivations

#kss_perms CertificateChecks.KernelSporSch.Co3K1 4 CFSG.Sporadic.Schreier.Co3.co3Kappa1Gens

namespace CertificateChecks.KernelSporSch.Co3Second

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.M11
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Sporadic.Mathieu
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

theorem m1c_lines : allN 8 (fun j => Nat.beq (Co3M1C.S j) (Co3Text.L (Nat.add 78 j))) = true := by
  quickRfl

theorem m1c_perm : allN 8 (fun j => permOK 276 9 (mask 9) (276 * 9) (Co3M1C.S j) (Co3M1C.SI j)) =
    true := by
  quickRfl

theorem m1c_binds : Binds 276 9 Co3M1C.S 8 4 Co3M1C.BP co3M1CommArrs co3M1CommBaseArr := by
  obtain ⟨hs, he⟩ := Co3Text.field_of (f := 9) rfl (by norm_num) m1c_lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

theorem m112_lines : allN 13 (fun j => Nat.beq (Co3M112.S j) (Co3Text12.L (Nat.add 0 j))) = true := by
  quickRfl

theorem m112_perm : allN 13 (fun j => permOK 12 4 (mask 4) (12 * 4) (Co3M112.S j) (Co3M112.SI j)) =
    true := by
  quickRfl

theorem m112_binds : Binds 12 4 Co3M112.S 13 5 Co3M112.BP co3M112Arrs co3M112BaseArr := by
  obtain ⟨hs, he⟩ := Co3Text12.field_of (f := 0) rfl (by norm_num) m112_lines
  exact ⟨by norm_num, by norm_num, by norm_num, hs, he, by decide, by decide⟩

@[expose] noncomputable def cm (i j : Nat) : Nat :=
  pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) (Co3M1.S j) (Co3M1.S i))
    (Co3M1.SI j)) (Co3M1.SI i)

@[expose] noncomputable def cmOK (k i j : Nat) : Bool :=
  bAnd(compEqK 276 9 (mask 9) (276 * 9) (Co3M1.S j) (Co3M1.S i)
    (pcomp 276 9 (mask 9) (Co3M1.S j) (Co3M1.S i)),
  bAnd(compEqK 276 9 (mask 9) (276 * 9) (pcomp 276 9 (mask 9) (Co3M1.S j) (Co3M1.S i))
    (Co3M1.SI j) (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) (Co3M1.S j) (Co3M1.S i)) (Co3M1.SI j)),
  bAnd(compEqK 276 9 (mask 9) (276 * 9)
    (pcomp 276 9 (mask 9) (pcomp 276 9 (mask 9) (Co3M1.S j) (Co3M1.S i)) (Co3M1.SI j))
    (Co3M1.SI i) (cm i j),
  Nat.beq (Co3M1C.S k) (cm i j))))

theorem cm0 : cmOK 0 1 4 = true := by quickRfl
theorem cm1 : cmOK 1 1 5 = true := by quickRfl
theorem cm2 : cmOK 2 2 5 = true := by quickRfl

theorem tt_hi : Co3Text.hiOK Co3Tt = true := by quickRfl

theorem tt_range : allN 276 (fun i => Nat.blt (pg 9 (mask 9) Co3Tt i) 276) = true := by quickRfl

theorem tt_sift : Bool.not (siftK 276 9 (mask 9) (276 * 9) (pidn 276 9) Co3M1C.LR Co3M1C.TRI
    Co3M1C.BP 4 0 Co3Tt) = true := by quickRfl

@[expose] noncomputable def ITP : Nat := packL 9 co3ItNat

@[expose] noncomputable def C12 : Nat := Co3Text12.L 13

theorem it_bind : bindListK 12 9 ITP co3ItNat = true := by quickRfl

theorem c12_line : allN 1 (fun j => Nat.beq C12 (Co3Text12.L (Nat.add 13 j))) = true := by quickRfl

theorem kappa_ok : allN 6 (fun k => kappaK 276 9 12 4 ITP C12 (pinvS 12 4 (mask 4) C12) (Co3M1.S k)
    (Co3K1 k)) = true := by quickRfl

theorem covers_ok : coversK 12 4 Co3K1 6 Co3M112.S 5 = true := by quickRfl

@[expose] def GAL : List Nat := [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def GBL : List Nat := [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

theorem gA_list : imageList m12gA = GAL := by decide

theorem gB_list : imageList m12gB = GBL := by decide

theorem gA_bind : bindListK 12 4 (packL 4 GAL) GAL = true := by quickRfl

theorem gB_bind : bindListK 12 4 (packL 4 GBL) GBL = true := by quickRfl

theorem gA_hi : Co3Text12.hiOK (packL 4 GAL) = true := by quickRfl

theorem gB_hi : Co3Text12.hiOK (packL 4 GBL) = true := by quickRfl

theorem gA_range : allN 12 (fun i => Nat.blt (pg 4 (mask 4) (packL 4 GAL) i) 12) = true := by
  quickRfl

theorem gB_range : allN 12 (fun i => Nat.blt (pg 4 (mask 4) (packL 4 GBL) i) 12) = true := by
  quickRfl

theorem gA_sift : siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) Co3M112.LR Co3M112.TRI Co3M112.BP 5 0
    (packL 4 GAL) = true := by quickRfl

theorem gB_sift : siftK 12 4 (mask 4) (12 * 4) (pidn 12 4) Co3M112.LR Co3M112.TRI Co3M112.BP 5 0
    (packL 4 GBL) = true := by quickRfl

theorem extract_get {S : Array (Array Nat)} {k j : Nat} (hj : j < k) (hk : k ≤ S.size) :
    (S.extract 0 k)[j]! = S[j]! := by
  rw [getElem!_pos (S.extract 0 k) j (by simp; omega), getElem!_pos S j (by omega)]
  simp

theorem comm_eq (k i j : Nat) (hi : i < 11) (hj : j < 11) (hk : k < 8) (h : cmOK k i j = true) :
    eqA 276 co3M1CommArrs[k]! (commA 276 co3M1Arrs i j) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
  have ij := (invEqK_sound (allN_spec Co3M1.perm j hj)).1
  have ii := (invEqK_sound (allN_spec Co3M1.perm i hi)).1
  rw [commA, Co3M1.arr_eq i hi, Co3M1.arr_eq j hj, ij, ii, compEqK_sound h1, compEqK_sound h3,
    compEqK_sound h5, m1c_binds.2.2.2.2.1 k hk, Nat.eq_of_beq_eq_true h6]
  exact eqK_sound (Nat.beq_refl _)

theorem kappa_eq (k : Nat) (hk : k < 6) :
    co3Kappa1Gens[k]! = unpack 12 4 (Co3K1 k) := by
  have hc : co3C12Arr = unpack 12 4 C12 :=
    (Co3Text12.field_of (f := 1) (F := fun _ => C12) rfl (by omega) c12_line).2 0 (by omega)
  rw [co3Kappa1Gens, getElem!_pos _ k (by simp; omega), Array.getElem_ofFn]
  change renameA 12 co3C12Arr (restrictA co3ItArr co3M1Arrs[k]!) = _
  rw [hc, co3ItArr, toArray_eq_of_bindListK it_bind, Co3M1.arr_eq k (by omega)]
  exact kappaK_sound (allN_spec kappa_ok k hk)

theorem facts : (rawChainOK 276 (co3M1CommArrs.extract 0 co3M1CommGenCount) co3M1CommArrs
        co3M1CommBaseArr (wordsArr co3M1CommGenCount co3M1CommStrongCount co3M1CommDerivations) 4 =
        true ∧
      rawOrbitSizes 276 co3M1CommArrs co3M1CommBaseArr = [132, 72, 5, 2])
    ∧ (rawChainOK 12 (co3M112Arrs.extract 0 co3M112GenCount) co3M112Arrs co3M112BaseArr
        (wordsArr co3M112GenCount co3M112StrongCount co3M112Derivations) 4 = true ∧
      rawOrbitSizes 12 co3M112Arrs co3M112BaseArr = [12, 11, 10, 9, 8])
    ∧ ((∀ k < 3, eqA 276 co3M1CommArrs[k]!
        (commA 276 co3M1Arrs ((co3M1CommPairs.getD k (0, 0)).1 - 1)
          ((co3M1CommPairs.getD k (0, 0)).2 - 1)) = true) ∧
      siftA 276 co3M1CommLevels co3M1CommBaseArr 0 co3TtArr = false ∧
      coversOK 12 co3Kappa1Gens (co3M112Arrs.extract 0 5) = true ∧
      siftA 12 co3M112Levels co3M112BaseArr 0 (imageList m12gA).toArray = true ∧
      siftA 12 co3M112Levels co3M112BaseArr 0 (imageList m12gB).toArray = true) := by
  refine ⟨⟨rawChainK_sound (NS := 18) (CH := 16) m1c_binds Co3M1C.head Co3M1C.hl (by norm_num)
      Co3M1C.hs, ?_⟩, ⟨rawChainK_sound (NS := 3) (CH := 4) m112_binds Co3M112.head Co3M112.hl
      (by norm_num) Co3M112.hs, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rawOrbitSizesK_sound m1c_binds m1c_perm Co3M1C.hl]
    decide
  · rw [rawOrbitSizesK_sound m112_binds m112_perm Co3M112.hl]
    decide
  · intro k hk
    interval_cases k
    · exact comm_eq 0 1 4 (by omega) (by omega) (by omega) cm0
    · exact comm_eq 1 1 5 (by omega) (by omega) (by omega) cm1
    · exact comm_eq 2 2 5 (by omega) (by omega) (by omega) cm2
  · rw [co3M1CommLevels, siftK_eq m1c_binds m1c_perm Co3M1C.hl Co3Single.tt_eq
      (Nat.eq_of_beq_eq_true tt_hi) tt_range]
    simpa using tt_sift
  · refine coversK_sound ⟨by simp [co3Kappa1Gens], kappa_eq⟩ ⟨?_, fun j hj => ?_⟩ covers_ok
    · simp [m112_binds.2.2.2.1]
    · rw [extract_get hj (by rw [m112_binds.2.2.2.1]; omega)]
      exact m112_binds.2.2.2.2.1 j (by omega)
  · rw [co3M112Levels, gA_list, toArray_eq_of_bindListK gA_bind]
    exact siftK_soundR m112_binds m112_perm Co3M112.hl rfl (Nat.eq_of_beq_eq_true gA_hi) gA_range
      gA_sift
  · rw [co3M112Levels, gB_list, toArray_eq_of_bindListK gB_bind]
    exact siftK_soundR m112_binds m112_perm Co3M112.hl rfl (Nat.eq_of_beq_eq_true gB_hi) gB_range
      gB_sift

end CertificateChecks.KernelSporSch.Co3Second

end

module

public import CFSG.Certificates.Kernel.Misc.YamakiAutMSound
public import Certificates.Kernel.Misc.YamakiAut.Final
public import Certificates.Kernel.Misc.YamakiAut.ChecksT
public import Certificates.Data.YamakiAmalgam
public import CFSG.Certificates.Kernel.Misc.YamakiNWSound

public section

namespace CFSG.KD.YamakiAutM

open CFSG.KC.YamakiAutM CFSG.KC.YamakiAut CFSG.KD.YamakiAut CFSG.KD.YamakiRepF CFSG.KD.YamakiRep
  CFSG.KC.YamakiS0 CFSG.KC.YamakiA0 CFSG.KD.YamakiA0 CFSG.KD.BfsK CFSG.KC.BfsEnum
  CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.KD.Sp62 (MULF ONE)

theorem ya550712_ta : wordN RH [0, 2, 4, 11, 8, 2, 10, 11, 8] = ta0 ∧
    wordN RH [3, 2, 6, 8, 11, 10] = ta1 ∧ wordN RH [7, 0, 6, 11, 8, 10, 11, 8] = tb0 ∧
    wordN RH [1, 2, 6, 8, 1, 11, 10] = tb1 := by
  decide +kernel

theorem ya550712_tau1A : tau1A () = #[arrN ta0, arrN ta1] := by
  have e : tau1A () = #[wordA (genA ()) [0, 2, 4, 11, 8, 2, 10, 11, 8],
      wordA (genA ()) [3, 2, 6, 8, 11, 10]] := rfl
  rw [e, wordA_eq yfH_gens _ (by decide), wordA_eq yfH_gens _ (by decide), ya550712_ta.1,
    ya550712_ta.2.1]

theorem ya550712_tau2A : tau2A () = #[arrN tb0, arrN tb1] := by
  have e : tau2A () = #[wordA (genA ()) [7, 0, 6, 11, 8, 10, 11, 8],
      wordA (genA ()) [1, 2, 6, 8, 1, 11, 10]] := rfl
  rw [e, wordA_eq yfH_gens _ (by decide), wordA_eq yfH_gens _ (by decide), ya550712_ta.2.2.1,
    ya550712_ta.2.2.2]

theorem ya550712_at : ∀ t < 23040, autAtT RH RT ta0 ta1 tb0 tb1 t = true :=
  autAtT_of_chunks (L := 512) (M := 45) (fun q hq => by
    have e := ch550712K.all q hq
    unfold ch550712C at e
    exact e) (by norm_num)

theorem ya550712_tab1 : autOK (enumH ()) (gH ()) (tau1A ()) (tabT1 ()) = true ∧
    ∀ t < 23040, (tabT1 ())[t]! = arrN (RT t % 2 ^ 36) := by
  unfold tabT1
  rw [ya550712_tau1A]
  exact autOK_of_mcodes (R := RH) (RP := fun t => RT t % 2 ^ 36) (n := 23040) (v0 := 31)
    (v1 := 165) enumH_repF.1 (by norm_num) enumH_repF.2.2.1 enumH_repF.2.2.2.1
    enumH_repF.2.2.2.2 ya550851_step (by simp [gH, wordsA, hWords]) ya550851_gens ch550851i
    (fun t ht => autAtT_left (ya550712_at t ht))

theorem ya550712_tab2 : autOK (enumH ()) (gH ()) (tau2A ()) (tabT2 ()) = true ∧
    ∀ t < 23040, (tabT2 ())[t]! = arrN (RT t / 2 ^ 36) := by
  unfold tabT2
  rw [ya550712_tau2A]
  exact autOK_of_mcodes (R := RH) (RP := fun t => RT t / 2 ^ 36) (n := 23040) (v0 := 31)
    (v1 := 165) enumH_repF.1 (by norm_num) enumH_repF.2.2.1 enumH_repF.2.2.2.1
    enumH_repF.2.2.2.2 ya550851_step (by simp [gH, wordsA, hWords]) ya550851_gens ch550851i
    (fun t ht => autAtT_right (ya550712_at t ht))

@[expose] def sPi : List Nat :=
  [0, 46, 31, 23, 54, 12, 32, 60, 39, 9, 30, 22, 5, 63, 53, 41, 34, 24, 52, 40, 20, 58, 11, 3, 17,
    43, 33, 61, 51, 29, 10, 2, 6, 26, 16, 42, 57, 49, 38, 8, 19, 15, 35, 25, 56, 48, 1, 47, 45, 37,
    50, 28, 18, 14, 4, 62, 44, 36, 21, 59, 7, 27, 55, 13]

@[expose] def sImg0 : List Nat :=
  [0, 19, 51, 32, 57, 42, 10, 25, 53, 38, 6, 21, 12, 31, 63, 44, 22, 5, 37, 54, 47, 60, 28, 15, 35,
    48, 16, 3, 26, 9, 41, 58, 56, 43, 11, 24, 1, 18, 50, 33, 13, 30, 62, 45, 52, 39, 7, 20, 46, 61,
    29, 14, 23, 4, 36, 55, 27, 8, 40, 59, 34, 49, 17, 2]

@[expose] def sImg1 : List Nat :=
  [0, 31, 33, 62, 61, 34, 28, 3, 45, 50, 12, 19, 16, 15, 49, 46, 52, 43, 21, 10, 9, 22, 40, 55, 25,
    6, 56, 39, 36, 59, 5, 26, 51, 44, 18, 13, 14, 17, 47, 48, 30, 1, 63, 32, 35, 60, 2, 29, 7, 24,
    38, 57, 58, 37, 27, 4, 42, 53, 11, 20, 23, 8, 54, 41]

@[expose] def sa0 : Nat := 6437682694

@[expose] def sa1 : Nat := 67464714351

theorem ya550712_sa : wordN RN [2, 6, 1, 10, 9] = sa0 ∧ wordN RN [6, 0, 8, 9, 10, 2, 0] = sa1 := by
  decide +kernel

theorem ya550712_sigmaA : sigmaA () = #[arrN sa0, arrN sa1] := by
  have e : sigmaA () = #[wordA (genA ()) [2, 6, 1, 10, 9], wordA (genA ()) [6, 0, 8, 9, 10, 2, 0]] :=
    rfl
  rw [e, wordA_eq yfN_gens _ (by decide), wordA_eq yfN_gens _ (by decide), ya550712_sa.1,
    ya550712_sa.2]

theorem ya550712_pi : ∀ x < 64, sPi.getD x 0 < 64 ∧ sPi.getD (sPi.getD x 0) 0 = x := by
  decide

theorem ya550712_pic : ∀ x < 64,
    sImg0.getD x 0 < 64 ∧ MULF (RN 12) (CFSG.KD.YamakiNA.vnum x) =
        CFSG.KD.YamakiNA.vnum (sImg0.getD x 0) ∧
      MULF sa0 (CFSG.KD.YamakiNA.vnum (sPi.getD x 0)) =
        CFSG.KD.YamakiNA.vnum (sPi.getD (sImg0.getD x 0) 0) ∧
    sImg1.getD x 0 < 64 ∧ MULF (RN 13) (CFSG.KD.YamakiNA.vnum x) =
        CFSG.KD.YamakiNA.vnum (sImg1.getD x 0) ∧
      MULF sa1 (CFSG.KD.YamakiNA.vnum (sPi.getD x 0)) =
        CFSG.KD.YamakiNA.vnum (sPi.getD (sImg1.getD x 0) 0) := by
  decide +kernel

theorem ya550712_piA (x : ℕ) (hx : x < 64) : (arrL 64 sPi)[x]! = sPi.getD x 0 := by
  rw [arrL_get hx, if_pos hx]

theorem ya550712_tabS : autOK (enumN ()) (gN ()) (sigmaA ()) (tabS ()) = true ∧
    ∀ t < 10752, (tabS ())[t]! = compA (compA (arrL 64 sPi) (arrN (recX RN 14 t))) (arrL 64 sPi) := by
  unfold tabS
  have hgs := ya550831_gens
  refine autOK_of_conj (T := fun t => arrN (recX RN 14 t)) (PA := recF RN 14 0)
    (PB := recF RN 14 1) (POS := recPOS RN 14 2) enumN_repF.1 (by norm_num)
    (by beta_reduce; rw [enumN_repF.2.2.1, arrN_one]) ?_ ?_ (fun t _ => arrN_size _)
    (fun t _ x hx => arrN_lt _ hx) (by simp [gN, wordsA, nWords])
    (fun j hj x hx => by rw [hgs j hj]; exact arrN_lt _ hx) ?_ ?_
  · intro i hi
    obtain ⟨b1, b2, b3⟩ := enumN_repF.2.2.2.1 i hi
    refine ⟨b1, b2, ?_⟩
    beta_reduce
    rw [b3, hgs _ b2, arrN_mul]
  · intro i hi
    obtain ⟨s1, s2⟩ := ya550831_step i hi
    refine ⟨s1, ?_⟩
    beta_reduce
    rw [s2, hgs _ (Nat.mod_lt _ (by norm_num)), arrN_mul]
  · intro x hx
    obtain ⟨p1, p2⟩ := ya550712_pi x hx
    rw [ya550712_piA x hx, ya550712_piA _ p1, p2]
    exact ⟨p1, p1, rfl, rfl⟩
  · intro j hj x hx
    obtain ⟨a1, a2, a3, b1, b2, b3⟩ := ya550712_pic x hx
    have hp := (ya550712_pi x hx).1
    rw [ya550712_sigmaA, hgs j hj, ya550712_piA x hx]
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · rw [(CFSG.KC.YamakiNW.arrN_get_iff hx a1).2 a2, ya550712_piA _ a1]
      exact ((CFSG.KC.YamakiNW.arrN_get_iff hp (ya550712_pi _ a1).1).2 a3).symm
    · rw [(CFSG.KC.YamakiNW.arrN_get_iff hx b1).2 b2, ya550712_piA _ b1]
      exact ((CFSG.KC.YamakiNW.arrN_get_iff hp (ya550712_pi _ b1).1).2 b3).symm

theorem crGenCheck_holds : crGenCheck () = true := by decide +kernel

theorem autCheck_holds : autCheck () = true := by
  unfold autCheck
  dsimp only
  rw [ya550712_tabS.1, ya550712_tab1.1, ya550712_tab2.1]
  rfl

end CFSG.KD.YamakiAutM

end

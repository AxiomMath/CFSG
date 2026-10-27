module

public import Certificates.Kernel.SporSch.Tits.Stab2270K
public import Certificates.Kernel.SporSch.Tits.Help
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.TitsStab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Monster.B.Co2
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelSpor.Tits2268 CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp

theorem hw14 : 8775 + 1 < 2 ^ 14 := by norm_num
theorem hw12 : 2925 + 1 < 2 ^ 12 := by norm_num
theorem hw11 : 1755 + 1 < 2 ^ 11 := by norm_num

theorem isInv_unpack {n w P R : Nat} (h : permW n w P R = true) :
    isInvA n (unpack n w P) (invCand n (unpack n w P)) = true := by
  rw [permW_eq] at h
  obtain ⟨h1, h2⟩ := invEqK_sound h
  rw [h1]
  exact h2

theorem inv_unpack {n w P R : Nat} (h : permW n w P R = true) :
    invCand n (unpack n w P) = unpack n w R := by
  rw [permW_eq] at h
  exact (invEqK_sound h).1

theorem eqA_self (n : Nat) (a : Array Nat) : eqA n a a = true := by
  unfold eqA
  rw [allLt_iff]
  intro i _
  simp

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem memN_contains (p : Nat) : ∀ L : List Nat, memN p L = L.contains p
  | [] => rfl
  | y :: L => by
    change Bool.rec (motive := fun _ => Bool) (memN p L) true (Nat.beq p y) = _
    rw [List.contains_cons, memN_contains p L, nat_beq]
    cases Nat.beq p y <;> rfl

theorem allN_two {f : Nat → Bool} (h : allN 13 f = true) : allN 2 f = true :=
  allN_of_forall fun i hi => allN_spec h i (by omega)

theorem flag_size : titsFlagArrs.size = 4 := by
  unfold titsFlagArrs
  simp

theorem flag_get {j : Nat} (hj : j < 4) : titsFlagArrs[j]! = unpack 8775 14 (T8775.F j) := by
  unfold titsFlagArrs
  rw [getElem!_ofFn_of_lt _ hj]
  exact arr8775_eq (by omega)

theorem star_size : titsAStarArrs.size = 4 := by
  unfold titsAStarArrs
  simp

theorem star_get {j : Nat} (hj : j < 4) : titsAStarArrs[j]! = unpack 2925 12 (T2925.F j) := by
  unfold titsAStarArrs
  rw [getElem!_ofFn_of_lt _ hj]
  exact arr2925_eq (by omega)

theorem fG' : allN 4 (fun j => permOK 8775 14 (mask 14) (8775 * 14) (T8775.F j) (TitsSF.GI j)) =
    true := by
  simpa only [permW_eq] using fG

theorem aG' : allN 4 (fun j => permOK 2925 12 (mask 12) (2925 * 12) (T2925.F j) (TitsSS.GI j)) =
    true := by
  simpa only [permW_eq] using aG

theorem fTp' : allN 13 (fun j => permOK 8775 14 (mask 14) (8775 * 14) (TitsSF.T j)
    (TitsSF.TI j)) = true := by
  simpa only [permW_eq] using fTp

theorem aTp' : allN 13 (fun j => permOK 2925 12 (mask 12) (2925 * 12) (TitsSS.T j)
    (TitsSS.TI j)) = true := by
  simpa only [permW_eq] using aTp

theorem uF {j : Nat} (hj : j < 2) :
    wordArr 8775 titsFlagArrs (titsU j) = unpack 8775 14 (TitsSF.U j) :=
  wordW_sound hw14 ⟨flag_size, fun _ hi => flag_get hi⟩ fG' ((bAnd_iff _ _).1 (allN_spec fU j hj)).1

theorem vF {j : Nat} (hj : j < 2) :
    wordArr 8775 titsFlagArrs (titsV j) = unpack 8775 14 (TitsSF.V j) :=
  wordW_sound hw14 ⟨flag_size, fun _ hi => flag_get hi⟩ fG' ((bAnd_iff _ _).1 (allN_spec fU j hj)).2

theorem uS {j : Nat} (hj : j < 2) :
    wordArr 2925 titsAStarArrs (titsU j) = unpack 2925 12 (TitsSS.U j) :=
  wordW_sound hw12 ⟨star_size, fun _ hi => star_get hi⟩ aG' ((bAnd_iff _ _).1 (allN_spec aU j hj)).1

theorem vS {j : Nat} (hj : j < 2) :
    wordArr 2925 titsAStarArrs (titsV j) = unpack 2925 12 (TitsSS.V j) :=
  wordW_sound hw12 ⟨star_size, fun _ hi => star_get hi⟩ aG' ((bAnd_iff _ _).1 (allN_spec aU j hj)).2

theorem dF_size : titsDFlagArrs.size = 2 := by
  unfold titsDFlagArrs
  simp

theorem dS_size : titsDStarArrs.size = 2 := by
  unfold titsDStarArrs
  simp

theorem dF_get {j : Nat} (hj : j < 2) : titsDFlagArrs[j]! = unpack 8775 14 (TitsSF.T j) := by
  unfold titsDFlagArrs
  rw [getElem!_ofFn_of_lt _ hj]
  dsimp only
  unfold commArr
  obtain ⟨hu, hv⟩ := (bAnd_iff _ _).1 (allN_spec fUp j hj)
  obtain ⟨c1, c23⟩ := (bAnd_iff _ _).1 (allN_spec fC j hj)
  obtain ⟨c2, c34⟩ := (bAnd_iff _ _).1 c23
  obtain ⟨c3, -⟩ := (bAnd_iff _ _).1 c34
  rw [uF hj, vF hj, inv_unpack hu, inv_unpack hv, eq2W_sound c1, eq2W_sound c2, eq2W_sound c3]

theorem dS_get {j : Nat} (hj : j < 2) : titsDStarArrs[j]! = unpack 2925 12 (TitsSS.T j) := by
  unfold titsDStarArrs
  rw [getElem!_ofFn_of_lt _ hj]
  dsimp only
  unfold commArr
  obtain ⟨hu, hv⟩ := (bAnd_iff _ _).1 (allN_spec aUp j hj)
  obtain ⟨c1, c23⟩ := (bAnd_iff _ _).1 (allN_spec aC j hj)
  obtain ⟨c2, c34⟩ := (bAnd_iff _ _).1 c23
  obtain ⟨c3, -⟩ := (bAnd_iff _ _).1 c34
  rw [uS hj, vS hj, inv_unpack hu, inv_unpack hv, eq2W_sound c1, eq2W_sound c2, eq2W_sound c3]

theorem tF_stored {j : Nat} (hj : j < 2) : TitsSF.T j = T8775.F (4 + j) := by
  obtain ⟨-, c23⟩ := (bAnd_iff _ _).1 (allN_spec fC j hj)
  obtain ⟨-, c34⟩ := (bAnd_iff _ _).1 c23
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 c34).2

theorem tS_stored {j : Nat} (hj : j < 2) : TitsSS.T j = T2925.F (4 + j) := by
  obtain ⟨-, c23⟩ := (bAnd_iff _ _).1 (allN_spec aC j hj)
  obtain ⟨-, c34⟩ := (bAnd_iff _ _).1 c23
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 c34).2

theorem len_W : 2 + titsDerivedDerivations.length = 13 := rfl

theorem strF : strongArrs 8775 titsDFlagArrs titsDerivedDerivations =
      Array.ofFn (n := 2 + titsDerivedDerivations.length) (fun j => unpack 8775 14 (TitsSF.T j.val)) ∧
    strongOK 8775 2 titsDFlagArrs (strongArrs 8775 titsDFlagArrs titsDerivedDerivations) titsDerivedDerivations =
      true := strongK_sound (W := titsDerivedDerivations) hw14
  ⟨dF_size, fun _ hi => dF_get hi⟩ (by rw [len_W]; exact fTp') fS

theorem strS : strongArrs 2925 titsDStarArrs titsDerivedDerivations =
      Array.ofFn (n := 2 + titsDerivedDerivations.length) (fun j => unpack 2925 12 (TitsSS.T j.val)) ∧
    strongOK 2925 2 titsDStarArrs (strongArrs 2925 titsDStarArrs titsDerivedDerivations) titsDerivedDerivations =
      true := strongK_sound (W := titsDerivedDerivations) hw12
  ⟨dS_size, fun _ hi => dS_get hi⟩ (by rw [len_W]; exact aTp') aS

theorem tF_size : titsTFlagArrs.size = 13 := by
  unfold titsTFlagArrs
  rw [strF.1]
  simp [len_W]

theorem tF_get {j : Nat} (hj : j < 13) : titsTFlagArrs[j]! = unpack 8775 14 (TitsSF.T j) := by
  unfold titsTFlagArrs
  rw [strF.1, getElem!_ofFn_of_lt _ (Nat.lt_of_lt_of_eq hj len_W.symm)]

theorem tS_size : titsTStarArrs.size = 13 := by
  unfold titsTStarArrs
  rw [strS.1]
  simp [len_W]

theorem tS_get {j : Nat} (hj : j < 13) : titsTStarArrs[j]! = unpack 2925 12 (TitsSS.T j) := by
  unfold titsTStarArrs
  rw [strS.1, getElem!_ofFn_of_lt _ (Nat.lt_of_lt_of_eq hj len_W.symm)]

theorem ptF {wd : List Int} (hl : lettersK 13 wd = true) {i : Nat} (hi : i < 8775) :
    (wordArr 8775 titsTFlagArrs wd)[i]! = wPtG 14 TitsSF.T TitsSF.TI wd i :=
  wPtG_sound hw14 ⟨tF_size, fun _ hj => tF_get hj⟩ fTp' hl hi

theorem ptS {wd : List Int} (hl : lettersK 13 wd = true) {i : Nat} (hi : i < 2925) :
    (wordArr 2925 titsTStarArrs wd)[i]! = wPtG 12 TitsSS.T TitsSS.TI wd i :=
  wPtG_sound hw12 ⟨tS_size, fun _ hj => tS_get hj⟩ aTp' hl hi

theorem ptD {wd : List Int} (hl : lettersK 13 wd = true) {i : Nat} (hi : i < 1755) :
    (wordArr 1755 titsDerivedArrs wd)[i]! = wPtG 11 TitsD.S TitsD.SI wd i :=
  wPtG_sound hw11 ⟨bindsD.2.2.2.1, bindsD.2.2.2.2.1⟩ permD hl hi

theorem fixW_spec {w : Nat} {T TI : Nat → Nat} {L : List Nat} {wd : List Int}
    (h : fixW w T TI L wd = true) :
    lettersK 13 wd = true ∧ ∀ f ∈ L, wPtG w T TI wd f = f := by
  obtain ⟨hl, ha⟩ := (bAnd_iff _ _).1 h
  exact ⟨hl, fun f hf => Nat.eq_of_beq_eq_true (allL_spec ha f hf)⟩

theorem five_lt {f : Nat} (hf : f ∈ titsFiveFlags) : f < 8775 := by
  have e : titsFiveFlags = [0, 2, 5, 10, 20] := rfl
  simp only [e, List.mem_cons, List.not_mem_nil, or_false] at hf
  omega

theorem three_lt {f : Nat} (hf : f ∈ titsThreeFlags) : f < 8775 := by
  have e : titsThreeFlags = [0, 1, 3] := rfl
  simp only [e, List.mem_cons, List.not_mem_nil, or_false] at hf
  omega

theorem all_congr' {α : Type} {f g : α → Bool} : ∀ {L : List α}, (∀ x ∈ L, f x = g x) →
    L.all f = L.all g
  | [], _ => rfl
  | x :: L, h => by
    rw [List.all_cons, List.all_cons, h x List.mem_cons_self,
      all_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem allL_all {f : Nat → Bool} : ∀ (L : List Nat), allL f L = L.all f
  | [] => rfl
  | x :: L => by
    change Bool.rec (motive := fun _ => Bool) false (allL f L) (f x) = (f x && L.all f)
    rw [allL_all L]
    cases f x <;> rfl

theorem pow_eq {wd : List Int} {k k' : Nat} {L : List Nat} (hr : rngW wd k' L = true)
    (hk : k ≤ k') : powFixes (wordArr 8775 titsTFlagArrs wd) k L = powW wd k L := by
  obtain ⟨hl, hR⟩ := (bAnd_iff _ _).1 hr
  unfold powFixes powW
  rw [allL_all]
  refine all_congr' fun p hp => ?_
  rw [iterA_eq (fun x hx => ptF hl hx) (itRng_le (allL_spec hR p hp) hk), nat_beq]
  rfl

theorem false_of {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

theorem facts : (∀ j < 2, isInvA 8775 (wordArr 8775 titsFlagArrs (titsU j))
        (invCand 8775 (wordArr 8775 titsFlagArrs (titsU j))) = true ∧
      isInvA 8775 (wordArr 8775 titsFlagArrs (titsV j))
        (invCand 8775 (wordArr 8775 titsFlagArrs (titsV j))) = true ∧
      isInvA 2925 (wordArr 2925 titsAStarArrs (titsU j))
        (invCand 2925 (wordArr 2925 titsAStarArrs (titsU j))) = true ∧
      isInvA 2925 (wordArr 2925 titsAStarArrs (titsV j))
        (invCand 2925 (wordArr 2925 titsAStarArrs (titsV j))) = true) ∧
    strongOK 8775 2 titsDFlagArrs titsTFlagArrs titsDerivedDerivations = true ∧
    strongOK 2925 2 titsDStarArrs titsTStarArrs titsDerivedDerivations = true ∧
    (∀ j < 2, eqA 8775 titsDFlagArrs[j]! titsDFlagStored[j]! = true ∧
      eqA 2925 titsDStarArrs[j]! titsDStarStored[j]! = true) ∧
    forestOK 8775 titsDFlagArrs #[0] = true ∧ forestOK 2925 titsDStarArrs #[0] = true ∧
    titsHWords.all (fun w => (wordArr 1755 titsDerivedArrs w)[0]! == 0) = true ∧
    titsSWords.all (fun w => (wordArr 8775 titsTFlagArrs w)[0]! == 0) = true ∧
    titsRWords.all (fun w => (wordArr 8775 titsTFlagArrs w)[0]! == 0) = true ∧
    titsNWords.all (fun w => (wordArr 2925 titsTStarArrs w)[0]! == 0) = true ∧
    titsJWords.all (fun w => titsFiveFlags.all fun f => (wordArr 8775 titsTFlagArrs w)[f]! == f) =
      true ∧
    titsKWords.all (fun w => titsThreeFlags.all fun f => (wordArr 8775 titsTFlagArrs w)[f]! == f) =
      true ∧
    titsFiveFlags = [0, 2, 5, 10, 20] ∧ titsThreeFlags = [0, 1, 3] ∧
    allLt 8775 (fun j => (titsBetaArr[j]! == 0) == titsFiveFlags.contains j) = true ∧
    allLt 8775 (fun j => (titsKappaArr[j]! == 0) == titsThreeFlags.contains j) = true ∧
    titsHWords = [[3], [4], [13]] ∧
    powFixes (wordArr 8775 titsTFlagArrs [3]) 4 titsFiveFlags = true ∧
    powFixes (wordArr 8775 titsTFlagArrs [3]) 2 titsFiveFlags = false ∧
    powFixes (wordArr 8775 titsTFlagArrs [3, 4, 13]) 5 titsFiveFlags = true ∧
    powFixes (wordArr 8775 titsTFlagArrs [3, 4, 13]) 1 titsFiveFlags = false ∧
    powFixes (wordArr 8775 titsTFlagArrs titsNWords[2]!) 2 titsThreeFlags = true ∧
    powFixes (wordArr 8775 titsTFlagArrs titsNWords[2]!) 1 titsThreeFlags = false ∧
    powFixes (wordArr 8775 titsTFlagArrs (titsNWords[2]! ++ titsNWords[3]!)) 3 titsThreeFlags =
      true ∧
    powFixes (wordArr 8775 titsTFlagArrs (titsNWords[2]! ++ titsNWords[3]!)) 1 titsThreeFlags =
      false := by
  refine ⟨fun j hj => ?_, strF.2, strS.2, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hu, hv⟩ := (bAnd_iff _ _).1 (allN_spec fUp j hj)
    obtain ⟨hu', hv'⟩ := (bAnd_iff _ _).1 (allN_spec aUp j hj)
    rw [uF hj, vF hj, uS hj, vS hj]
    exact ⟨isInv_unpack hu, isInv_unpack hv, isInv_unpack hu', isInv_unpack hv'⟩
  · have e1 : titsDFlagStored[j]! = unpack 8775 14 (T8775.F (4 + j)) := by
      unfold titsDFlagStored
      rw [getElem!_ofFn_of_lt _ hj]
      exact arr8775_eq (by omega)
    have e2 : titsDStarStored[j]! = unpack 2925 12 (T2925.F (4 + j)) := by
      unfold titsDStarStored
      rw [getElem!_ofFn_of_lt _ hj]
      exact arr2925_eq (by omega)
    rw [dF_get hj, dS_get hj, e1, e2, tF_stored hj, tS_stored hj]
    exact ⟨eqA_self _ _, eqA_self _ _⟩
  · exact forest1K_sound (GSI := TitsSF.TI) hw14 ⟨dF_size, fun _ hi => dF_get hi⟩ (allN_two fTp')
      fF
  · exact forest1K_sound (GSI := TitsSS.TI) hw12 ⟨dS_size, fun _ hi => dS_get hi⟩ (allN_two aTp')
      aF
  · rw [List.all_eq_true]
    intro wd hwd
    obtain ⟨hl, hf⟩ := fixW_spec (allA_spec kH wd hwd)
    rw [ptD hl (by norm_num), hf 0 List.mem_cons_self]
    rfl
  · rw [List.all_eq_true]
    intro wd hwd
    obtain ⟨hl, hf⟩ := fixW_spec (allA_spec kS wd hwd)
    rw [ptF hl (by norm_num), hf 0 List.mem_cons_self]
    rfl
  · rw [List.all_eq_true]
    intro wd hwd
    obtain ⟨hl, hf⟩ := fixW_spec (allA_spec kR wd hwd)
    rw [ptF hl (by norm_num), hf 0 List.mem_cons_self]
    rfl
  · rw [List.all_eq_true]
    intro wd hwd
    obtain ⟨hl, hf⟩ := fixW_spec (allA_spec kN wd hwd)
    rw [ptS hl (by norm_num), hf 0 List.mem_cons_self]
    rfl
  · rw [List.all_eq_true]
    intro wd hwd
    obtain ⟨hl, hf⟩ := fixW_spec (allA_spec kJ wd hwd)
    rw [List.all_eq_true]
    intro f hfm
    rw [ptF hl (five_lt hfm), hf f hfm]
    exact beq_self_eq_true f
  · rw [List.all_eq_true]
    intro wd hwd
    obtain ⟨hl, hf⟩ := fixW_spec (allA_spec kK wd hwd)
    rw [List.all_eq_true]
    intro f hfm
    rw [ptF hl (three_lt hfm), hf f hfm]
    exact beq_self_eq_true f
  · rw [allLt_iff]
    intro j hj
    have h := allN_spec kB j hj
    rw [beqB_eq, pgW_eq, ← nat_beq, memN_contains] at h
    rw [beta_eq, unpackW_get hj]
    exact h
  · rw [allLt_iff]
    intro j hj
    have h := allN_spec kK3 j hj
    rw [beqB_eq, pgW_eq, ← nat_beq, memN_contains] at h
    rw [kappa_eq, unpackW_get hj]
    exact h
  · rw [pow_eq r1 le_rfl]
    exact p1
  · rw [pow_eq r1 (by norm_num)]
    exact false_of p2
  · rw [pow_eq r2 le_rfl]
    exact p3
  · rw [pow_eq r2 (by norm_num)]
    exact false_of p4
  · rw [pow_eq r3 le_rfl]
    exact p5
  · rw [pow_eq r3 (by norm_num)]
    exact false_of p6
  · rw [pow_eq r4 le_rfl]
    exact p7
  · rw [pow_eq r4 (by norm_num)]
    exact false_of p8

end CertificateChecks.KernelSporSch.TitsStab

end

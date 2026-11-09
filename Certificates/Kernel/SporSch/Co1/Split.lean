module

public import Certificates.Kernel.SporSch.Co1.SplitK
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Split

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.Orb CFSG.KS.Mathieu
open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
open CertificateChecks.KernelSporSch.Co1Packed CertificateChecks.KernelSporSch.Co1Elem

theorem ngetL_eq : ∀ (l : List (List Nat)) (i : Nat), ngetL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => ngetL_eq l i

theorem a_eq : aR = unpack 24 24 (AB 0) := by rw [aR_u, Nat.eq_of_beq_eq_true kAB0]
theorem b_eq : bR = unpack 24 24 (AB 1) := by rw [bR_u, Nat.eq_of_beq_eq_true kAB1]
theorem ai_eq : inv aR = unpack 24 24 (ABI 0) := by
  rw [aR_u]
  exact (invOKK_sound ((bAnd_iff (invOKK PA (ABI 0)) (invOKK PB (ABI 1))).1 kab).1).2
theorem bi_eq : inv bR = unpack 24 24 (ABI 1) := by
  rw [bR_u]
  exact (invOKK_sound ((bAnd_iff (invOKK PA (ABI 0)) (invOKK PB (ABI 1))).1 kab).2).2

theorem ab_list : [unpack 24 24 (AB 0), unpack 24 24 (AB 1)] =
    (List.range 2).map fun i => unpack 24 24 (AB i) := rfl
theorem abi_list : [unpack 24 24 (ABI 0), unpack 24 24 (ABI 1)] =
    (List.range 2).map fun i => unpack 24 24 (ABI i) := rfl

theorem amb_eq : hAmbRows = (List.range 2).map fun i => unpack 24 24 (SG.M i) := by
  unfold hAmbRows
  rw [ai_eq, bi_eq, a_eq, b_eq, ab_list, abi_list]
  apply List.ext_getElem
  · simp [Nat.eq_of_beq_eq_true kNb]
  · intro i h1 h2
    have hi : i < 2 := by simpa using h2
    have hk := allN_spec kAmb i hi
    rw [ngetL_eq] at hk
    simp only [List.getElem_map, List.getElem_range]
    rw [← wordSK_sound hk, List.getD_eq_getElem _ _ (by simpa using h1)]

theorem dag_eq : strongDag = ((List.range SG.N).map fun i => unpack 24 24 (SG.M i),
    (List.range SG.N).map fun i => unpack 24 24 (SG.MI i), true) := by
  unfold strongDag
  exact dagWK_sound amb_eq kSD

theorem gRows_eq : gRows = fun i => unpack 24 24 (GF i) := by
  funext i
  have hv : gRows i = unpack 24 24 (GV i) := by
    unfold gRows GV
    rw [dag_eq, ai_eq, bi_eq, a_eq, b_eq, ab_list, abi_list]
    dsimp only
    apply gValK_sound
    rcases Nat.lt_or_ge i 3 with hi | hi
    · exact ((bAnd_iff (gLettersK SG.N (Data.topWords.getD i []) (Data.lowerWords.getD i []))
        (Nat.beq (GV i) (GG i))).1 (allN_spec kG i hi)).1
    · have ht : Data.topWords.getD i [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [Data.topWords]; omega),
          Option.getD_none]
      have hl : Data.lowerWords.getD i [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [Data.lowerWords]; omega),
          Option.getD_none]
      rw [ht, hl]
      rfl
  rw [hv]
  unfold GF
  rcases Nat.lt_or_ge i 3 with hi | hi
  · have hb : Nat.blt i 3 = true := Nat.blt_eq.mpr hi
    rw [hb, Nat.eq_of_beq_eq_true ((bAnd_iff
      (gLettersK SG.N (Data.topWords.getD i []) (Data.lowerWords.getD i []))
      (Nat.beq (GV i) (GG i))).1 (allN_spec kG i hi)).2]
  · have hb : Nat.blt i 3 = false := by
      rw [Bool.eq_false_iff]
      intro h
      have := Nat.blt_eq.mp h
      omega
    rw [hb]

theorem f4Hi_eq : f4Hi = f4HiP zR := rfl

theorem zPow_eq : zPow = zPowP zR := rfl

theorem qNat_eq : qNat = qNatP zR Data.f4vecs := by
  funext j
  unfold qNat qNatP
  rw [f4Hi_eq]

theorem zqT_eq : zqT = zqTP zR Data.f4vecs := by
  unfold zqT zqTP
  rw [zPow_eq, qNat_eq]

theorem zq_eq : zq = zqP zR Data.f4vecs := by
  funext e k
  unfold zq zqP
  rw [zqT_eq]

theorem msSearchB_match_eq : @msSearchB.match_1 = @msSearchP.match_1 := rfl

theorem msSearchB_P (Z : Rows) (fv : List (List Nat)) (X : Rows) (j : Nat) :
    msSearchB (zqP Z fv) (zqTP Z fv) X j = msSearchP Z fv X j := by
  unfold msSearchB msSearchP
  rw [msSearchB_match_eq]

theorem msSearch_eq : msSearch = msSearchP zR Data.f4vecs := by
  funext X j
  rw [msSearch, zq_eq, zqT_eq]
  exact msSearchB_P zR Data.f4vecs X j

theorem msSgn_eq : msSgn = msSgnP zR Data.f4vecs := by
  funext X j
  unfold msSgn msSgnP
  rw [msSearch_eq]

theorem msOK_eq : msOK = msOKP zR Data.f4vecs := by
  funext X
  unfold msOK msOKP
  rw [msSearch_eq, zq_eq]

theorem split_h : splitCheck = splitCheckP aR bR strongDag.2.2 gRows aRows zR Data.f4vecs
    Data.liftRows := by
  unfold splitCheck splitGens splitCheckP
  rw [msOK_eq]

theorem split_r : splitCheckP aR bR strongDag.2.2 gRows aRows zR Data.f4vecs Data.liftRows =
    true := by
  rw [aR_u, bR_u, dag_eq, gRows_eq, aRows_eq, zR_eq]
  refine splitK_sound (AI := ABI 0) (BI := ABI 1) kab kZ (fun i hi => ?_) kGens
  interval_cases i
  exacts [kLR0, kLR1, kLR2]

theorem split : splitCheck = true := by
  rw [split_h]
  exact split_r

theorem data_h : splitDataCheck = splitDataCheckP gRows aRows zR Data.f4vecs Data.liftPerms
    Data.liftSigns := by
  unfold splitDataCheck splitDataCheckP
  rw [msSearch_eq, msSgn_eq]

theorem data_r : splitDataCheckP gRows aRows zR Data.f4vecs Data.liftPerms Data.liftSigns =
    true := by
  rw [gRows_eq, aRows_eq, zR_eq]
  exact splitDataK_sound kZ kData

theorem data : splitDataCheck = true := by
  rw [data_h]
  exact data_r

theorem conj : splitConjCheck = true := by
  have h : splitConjCheck = splitConjCheckP gRows aRows Data.conjExps Data.corrExps := by
    unfold splitConjCheck splitConjCheckP eRows eRowsP
    rfl
  rw [h, gRows_eq, aRows_eq]
  exact conjK_sound kConj

theorem zqc : zqCheck = true := by
  have h : zqCheck = zqCheckP zR Data.f4vecs := by
    unfold zqCheck zq zqT qNat f4Hi zPow zqCheckP zqP zqTP qNatP f4HiP zPowP
    rfl
  rw [h, zR_eq]
  exact zqK_sound kZ kZD

end CertificateChecks.KernelSporSch.Co1Split

end

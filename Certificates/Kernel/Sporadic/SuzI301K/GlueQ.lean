module

public import Certificates.Kernel.Sporadic.SuzI301K.GlueDeg
public import CFSG.Certificates.Kernel.B0SuzK.Glue
public import CFSG.Certificates.Kernel.SuzI301LinSound
public import CFSG.Certificates.Kernel.LinRep.CheckSound
public import Certificates.Kernel.Sporadic.SuzI301K.Words

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin CFSG.KC.SuzI301K
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.RankThree.Native
open CFSG.Sporadic.SuzI301 CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0
  CFSG.PSL3Four.Native CFSG.KC.B0SuzK CertificateChecks.KernelLC

theorem pQ {i : Nat} (hi : i < 6) : PP 1782 11 (SuzB0Q.F i) :=
  ((baseK_facts B0Suz.kBase).2.2.2.1 i hi).1

theorem qe_eq {j : Nat} (hj : j < 128) : qElts[j]! = unpack 1782 11 (SuzB0QE j) := by
  obtain ⟨hT, -, -, hQ, hQP, hQE⟩ := baseK_facts B0Suz.kBase
  have hP : ∀ i < 6, PP 1782 11 (SuzB0Q.F i) := fun i hi => (hQ i hi).1
  have hq : ∀ i < 6, qArr i = unpack 1782 11 (SuzB0Q.F i) := fun i hi => B0Suz.q_eq hi
  have hj2 : j / 2 < 64 := by omega
  have hPQP : PP 1782 11 (SuzB0QP (j / 2)) := by
    rw [hQP _ hj2]
    exact (qProdK_spec hP hq _).1
  have hqs : qProds[j / 2]! = unpack 1782 11 (SuzB0QP (j / 2)) := by
    rw [hQP _ hj2]
    unfold qProds
    rw [getElem!_pos _ (j / 2) (by simpa using hj2), Array.getElem_ofFn]
    exact (qProdK_spec hP hq _).2
  unfold qElts
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  dsimp only
  unfold tPow
  rw [hqs, tPow_unpack B0Suz.t_eq, compA_PP hPQP (PP_tPowK hT _), hQE j hj, shiftRight_one_eq,
    land_one_eq]
  rfl

theorem pQE {j : Nat} (hj : j < 128) : PP 1782 11 (SuzB0QE j) := by
  obtain ⟨hT, -, -, hQ, hQP, hQE⟩ := baseK_facts B0Suz.kBase
  have hP : ∀ i < 6, PP 1782 11 (SuzB0Q.F i) := fun i hi => (hQ i hi).1
  rw [hQE j hj, hQP _ (by rw [shiftRight_one_eq]; omega)]
  exact (qProdK_spec hP (fun i hi => B0Suz.q_eq hi) _).1.mul (PP_tPowK hT _)

theorem qe_dist {j j' : Nat} (hj : j < 128) (hj' : j' < 128) (h : j ≠ j') :
    eqA 1782 qElts[j]! qElts[j']! = false := by
  have k := B0Suz.b0SuzCheck_true
  unfold b0SuzCheck at k
  simp only [Bool.and_eq_true] at k
  have k6 := k.1.1.1.1.2
  simp only [allBelow, List.all_eq_true, List.mem_range] at k6
  have e := k6 j hj j' hj'
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at e
  rcases e with e | e
  · exact absurd e h
  · exact e

theorem find_range {p : Nat → Bool} {J : Nat} :
    ∀ n, J < n → p J = true → (∀ j < n, p j = true → j = J) → (List.range n).find? p = some J
  | 0, hJ, _, _ => absurd hJ (Nat.not_lt_zero _)
  | n + 1, hJ, hp, hu => by
    rw [List.range_succ, List.find?_append]
    by_cases hn : J < n
    · rw [find_range n hn hp fun j hj => hu j (by omega)]
      rfl
    · have e : J = n := by omega
      have hnone : (List.range n).find? p = none := by
        rw [List.find?_eq_none]
        intro x hx hpx
        have := hu x (by simp at hx; omega) hpx
        simp at hx
        omega
      rw [hnone, e]
      simp [← e, hp]

theorem qIdx_eq {C : Nat} {Jf : Nat → Nat} (hC : permB 1782 11 C = true)
    (hk : crdK C SuzB0Q.F SuzB0QE Jf = true) {i : Nat} (hi : i < 6) :
    qIdx (unpack 1782 11 C) (invCand 1782 (unpack 1782 11 C)) i = Jf i ∧ Jf i < 128 := by
  unfold crdK at hk
  have e := allN_spec hk i hi
  beta_reduce at e
  obtain ⟨hlt, hb⟩ := band e
  have hJ : Jf i < 128 := Nat.blt_eq.mp hlt
  have hq' : permB 1782 11 (SuzB0Q.F i) = true := permB_of_pp (pQ hi)
  have hi' := permB_pinvS hw hC
  have hc : conj1782 (unpack 1782 11 C) (invCand 1782 (unpack 1782 11 C)) (qArr i) =
      qElts[Jf i]! := by
    unfold conj1782
    rw [B0Suz.q_eq hi, invCand_PP (pp_of_permB hw hC), comp_unpack' hw hq' hi',
      comp_unpack' hw hC (permB_pcomp hw hq' hi'), qe_eq hJ, ← Nat.eq_of_beq_eq_true hb]
    rfl
  have hself : eqA 1782 qElts[Jf i]! qElts[Jf i]! = true := by
    rw [qe_eq hJ, eqA_PP (pQE hJ) (pQE hJ)]
    exact Nat.beq_refl _
  refine ⟨?_, hJ⟩
  unfold qIdx
  rw [hc, find_range 128 hJ hself fun j hj hp => ?_]
  · rfl
  · by_contra hne
    rw [qe_dist hJ hj (Ne.symm hne)] at hp
    exact absurd hp (by decide)

theorem coords_of {C : Nat} {Jf : Nat → Nat} (hC : permB 1782 11 C = true)
    (hk : crdK C SuzB0Q.F SuzB0QE Jf = true) : coordsOK (unpack 1782 11 C) = true := by
  unfold coordsOK
  simp only [allBelow, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  intro i hi
  rw [(qIdx_eq hC hk hi).1]
  exact (qIdx_eq hC hk hi).2

theorem mat64_J {C : Nat} {Jf : Nat → Nat} (hC : permB 1782 11 C = true)
    (hk : crdK C SuzB0Q.F SuzB0QE Jf = true) :
    mat64 (unpack 1782 11 C) = CFSG.KC.LinRepSound.linTab (fun i => Jf i / 2) := by
  rw [CFSG.KC.SuzI301Lin.mat64_eq]
  exact CFSG.KC.LinRepSound.linTab_congr fun i hi => by rw [(qIdx_eq hC hk hi).1]

theorem crdD : crdK (SuzHS.F 1) SuzB0Q.F SuzB0QE (J 0) = true := kCrdD
theorem crdB2 : crdK (SuzHS.F 2) SuzB0Q.F SuzB0QE (J 1) = true := kCrdB2
theorem crdB3 : crdK (SuzHS.F 3) SuzB0Q.F SuzB0QE (J 2) = true := kCrdB3
theorem crdT : crdK TAU SuzB0Q.F SuzB0QE (J 3) = true := kCrdT

theorem coords_facts : coordsOK (sD ()) = true ∧ coordsOK (sB2 ()) = true ∧
    coordsOK (sB3 ()) = true ∧ coordsOK (sTau ()) = true := by
  rw [d_eq, b2_eq, b3_eq, tau_eq]
  exact ⟨coords_of pD crdD, coords_of pB2 crdB2, coords_of pB3 crdB3, coords_of pTAU crdT⟩

theorem mat64_D : mat64 (sD ()) = CFSG.KC.LinRepSound.linTab (fun i => J 0 i / 2) := by
  rw [d_eq]
  exact mat64_J pD crdD

theorem mat64_B2 : mat64 (sB2 ()) = CFSG.KC.LinRepSound.linTab (fun i => J 1 i / 2) := by
  rw [b2_eq]
  exact mat64_J pB2 crdB2

theorem mat64_B3 : mat64 (sB3 ()) = CFSG.KC.LinRepSound.linTab (fun i => J 2 i / 2) := by
  rw [b3_eq]
  exact mat64_J pB3 crdB3

theorem mat64_T : mat64 (sTau ()) = CFSG.KC.LinRepSound.linTab (fun i => J 3 i / 2) := by
  rw [tau_eq]
  exact mat64_J pTAU crdT

theorem J_lt {c i : Nat} (hc : c < 4) (hi : i < 6) : J c i < 128 := by
  have h : ∀ c < 4, crdK (match c with | 0 => SuzHS.F 1 | 1 => SuzHS.F 2 | 2 => SuzHS.F 3 | _ => TAU)
      SuzB0Q.F SuzB0QE (J c) = true := by
    intro c hc
    interval_cases c
    · exact crdD
    · exact crdB2
    · exact crdB3
    · exact crdT
  have e := allN_spec (h c hc) i hi
  beta_reduce at e
  exact Nat.blt_eq.mp (band e).1

theorem cw_col {c i : Nat} (hc : c < 4) (hi : i < 6) :
    CFSG.KC.LinRepSound.col (CFSG.KC.LinRep.nthN CFSG.KD.SuzI301.CW c) i = J c i / 2 := by
  have e := allN_spec kCW c hc
  beta_reduce at e
  have hs : ∀ (y : Nat) (k : Nat → Bool), strictB y k = k y := fun y k => by cases y <;> rfl
  rw [hs] at e
  have hw := Nat.eq_of_beq_eq_true e
  have hl : ∀ k < 6, hq CFSG.KD.SuzI301.QJ (Nat.add (Nat.mul 6 c) k) < 64 := fun k hk => by
    unfold hq
    rw [shiftRight_one_eq]
    have := J_lt hc hk
    unfold J at this
    omega
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := CFSG.KC.LinRepCheck.col_w6 (hl 0 (by norm_num))
    (hl 1 (by norm_num)) (hl 2 (by norm_num)) (hl 3 (by norm_num)) (hl 4 (by norm_num))
    (hl 5 (by norm_num))
  have hJ : ∀ k, hq CFSG.KD.SuzI301.QJ (Nat.add (Nat.mul 6 c) k) = J c k / 2 := fun k => by
    unfold hq J
    rw [shiftRight_one_eq]
  rw [hw]
  rcases CFSG.KC.LinRepSound.six_cases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← hJ 0]
    exact e0
  · rw [← hJ 1]
    exact e1
  · rw [← hJ 2]
    exact e2
  · rw [← hJ 3]
    exact e3
  · rw [← hJ 4]
    exact e4
  · rw [← hJ 5]
    exact e5

end CertificateChecks.KernelSpor.SuzI301K

end

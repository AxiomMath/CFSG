module

public import Certificates.Kernel.Misc.Perm.C2M

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Mathieu (powArr)
open CFSG.Monster.B.Fischer (ArrCert)

theorem d_conj : allLt 3 (fun k => allLt 2 fun l => co2FiveDLit.pts.toList.any
    (eqA 2300 (conjA 2300 co2FiveC1GenArrs[k]! co2FiveDGenArrs[l]!))) = true := by
  obtain ⟨hN, hP, -, -⟩ := litD
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro l hl
  obtain ⟨h1, h2⟩ := c1_parts.2.2.1 k hk l hl
  rw [C1gen k hk, Dgen l hl, conj_good (C1genI k hk) (gGD l hl)]
  exact any_good hN hP h1 h2

theorem d_comm : allLt 3 (fun k => allLt 3 fun l => co2FiveDLit.pts.toList.any
    (eqA 2300 (commutatorA 2300 co2FiveC1GenArrs[k]! co2FiveC1GenArrs[l]!))) = true := by
  obtain ⟨hN, hP, -, -⟩ := litD
  rw [allLt_iff]
  intro k hk
  rw [allLt_iff]
  intro l hl
  obtain ⟨h1, h2⟩ := c1_parts.2.2.2.1 k hk l hl
  have e := commutatorA_permOfMat hd22 sys.nodup sys.lt (C1genI k hk) (C1genI l hl)
  rw [V_size, ← hmm, ← hmm, ← hmm] at e
  rw [C1gen k hk, C1gen l hl, e]
  exact any_good hN hP h1 h2

theorem d_nonab : commA 2300 co2FiveDGenArrs[0]! co2FiveDGenArrs[1]! = false := by
  rw [Dgen 0 (by norm_num), Dgen 1 (by norm_num),
    commA_good (gGD 0 (by norm_num)) (gGD 1 (by norm_num))]
  exact c1_parts.2.2.2.2.1

theorem dinv_parts : DIt 0 = I22 ∧ ∀ i < 60, i ≠ 0 →
    DIt i = mmK (GDI (f12 (HDL.F 0) i)) (DIt (f12 (HDR.F 0) i)) := by
  have h := dinv_ok
  unfold dinvK at h
  rw [Bool.and_eq_true] at h
  refine ⟨Nat.eq_of_beq_eq_true h.1, fun i hi hi0 => ?_⟩
  have := allN_spec h.2 (i - 1) (by omega)
  have e : Nat.add (i - 1) 1 = i := by
    simp only [Nat.add_eq]
    omega
  rw [e] at this
  exact Nat.eq_of_beq_eq_true this

theorem d_words : CFSG.RankThree.PartOne.conjWordsOK 2300 co2FiveDLit co2FiveDGenArrs
    co2FiveSimpSel co2FiveSimpW = true := by
  obtain ⟨hN, hP, -, -⟩ := litD
  have hinv := tree_inv hd22 sys.lt hmm I22_eq (PMI := DIt) DgenI
    (Nat.eq_of_beq_eq_true rootD) dinv_parts.1 ptD_all dinv_parts.2
  have h := conjWordsOK_of_conjWordsM sys spans hmm I22_eq (ngen := 2) (N := 60) (GM := GD)
    (PM := PD) (PMI := DIt) (by rfl) Dgen (fun k hk => (gGD k hk).2) (fun k hk => (gGD k hk).1)
    hN hP hinv words_ok
  rwa [V_size] at h

theorem d_cent : allLt 600 (fun k => !(commA 2300 co2FiveC1Lit.pts[k]! co2FiveDGenArrs[0]! &&
    commA 2300 co2FiveC1Lit.pts[k]! co2FiveDGenArrs[1]!) ||
    (List.range 5).any fun e => eqA 2300 co2FiveC1Lit.pts[k]! (powArr 2300 co2FiveX1Arr e)) =
    true := by
  obtain ⟨hN, hP, -, -⟩ := litC1
  rw [allLt_iff]
  intro k hk
  have h := c1_parts.2.2.2.2.2 k hk
  rw [Dgen 0 (by norm_num), Dgen 1 (by norm_num), hP k hk, hX1,
    commA_good (gC1 k hk) (gGD 0 (by norm_num)), commA_good (gC1 k hk) (gGD 1 (by norm_num))]
  rw [Bool.or_eq_true] at h ⊢
  exact h.imp id (any_pow (gC1 k hk) (good_AM (by norm_num)))

theorem t_valid : validA 2300 co2FiveTArr = true := by
  rw [co2FiveTArr, arr_eq (by norm_num)]
  exact validA_inv (amF (k := 8) (by norm_num)).1

end CertificateChecks.KernelMisc.Co2K

end

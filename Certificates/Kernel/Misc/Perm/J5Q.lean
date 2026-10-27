module

public import Certificates.Kernel.Misc.Perm.J5S
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CFSG.KC.Misc.Clos (allN_iff anyN_iff)
open CFSG.Monster.B.Co2 (allLt_iff)

@[expose] noncomputable def I : ℕ := pidn 315 9

theorem hI : idA 315 = unpack 315 9 I := (idK_sound (by quickRfl)).symm

theorem pI : permB 315 9 I = true := by quickRfl

theorem pLX : ∀ j < 6, permB 315 9 (LX j) = true := (allN_iff _ _).1 (by quickRfl)

theorem pQG : ∀ k < 2, permB 315 9 (QG k) = true := (allN_iff _ _).1 (by quickRfl)

theorem gensValid : (List.range 3).all (fun k => validA 315 j2FiveGensR[k]!) = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [hGR k hk]
  interval_cases k
  · exact validA_unpack (r := pinvS 315 9 (mask 9) (GR 0)) (by quickRfl)
  · exact validA_unpack (r := pinvS 315 9 (mask 9) (GR 1)) (by quickRfl)
  · exact validA_unpack (r := pinvS 315 9 (mask 9) (GR 2)) (by quickRfl)

theorem pow_eq {p : ℕ} (hp : permB 315 9 p = true) (e : ℕ) :
    CFSG.Monster.B.Mathieu.powArr 315 (unpack 315 9 p) e = unpack 315 9 (pw p e) :=
  pow_unpack' hw hp e

theorem pPw {p : ℕ} (hp : permB 315 9 p = true) (e : ℕ) : permB 315 9 (pw p e) = true :=
  permB_ppow hw hp e

theorem q3 : CFSG.KC.LQT.P.allN 25 (fun k => Nat.beq (pw (QP.F k) 5) I) = true := by quickRfl

theorem q4 : CFSG.KC.LQT.P.allN 25 (fun k => Nat.beq (QP.F k) I ||
    CFSG.KC.LQT.P.anyN 6 fun j => CFSG.KC.LQT.P.anyN 5 fun e => Nat.beq (QP.F k) (pw (LX j) e)) =
    true := by quickRfl

theorem q5 : CFSG.KC.LQT.P.allN 6 (fun j => CFSG.KC.LQT.P.allN 6 fun j' => Nat.beq j j' ||
    CFSG.KC.LQT.P.allN 5 fun e => !(Nat.beq (LX j) (pw (LX j') e))) = true := by quickRfl

theorem q6 : CFSG.KC.LQT.P.allN 6 (fun j => invEqK 315 9 (mask 9) (315 * 9) (LX j)
    (pinvS 315 9 (mask 9) (LX j)) && Nat.beq (pw (LX j) 5) I && !(Nat.beq (LX j) I) &&
    memK 25 QP.F (LX j)) = true := by quickRfl

theorem q7 : CFSG.KC.LQT.P.allN 2 (fun k => Nat.beq (Nat.shiftRight (QG k) (315 * 9)) 0 &&
    sP (QG k)) = true := by quickRfl

theorem qCheck : j2FiveQCheck j2FiveQCert = true := by
  simp only [j2FiveQCheck, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨enumQ, bQ.1⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [bQ.2.1 k hk, pow_eq (pQ k hk), hI, eqA_unpack' hw (pPw (pQ k hk) 5) pI]
    exact (allN_iff _ _).1 q3 k hk
  · rw [allLt_iff]
    intro k hk
    have h := (allN_iff _ _).1 q4 k hk
    rw [Bool.or_eq_true, anyN_iff] at h
    rw [bQ.2.1 k hk, Bool.or_eq_true, hI, eqA_unpack' hw (pQ k hk) pI]
    rcases h with h | ⟨j, hj, h⟩
    · exact Or.inl h
    · right
      rw [anyN_iff] at h
      obtain ⟨e, he, h⟩ := h
      refine List.any_eq_true.2 ⟨j, List.mem_range.2 hj, List.any_eq_true.2
        ⟨e, List.mem_range.2 he, ?_⟩⟩
      rw [hLX j hj, pow_eq (pLX j hj), eqA_unpack' hw (pQ k hk) (pPw (pLX j hj) e)]
      exact h
  · rw [allLt_iff]
    intro j hj
    rw [allLt_iff]
    intro j' hj'
    have h := (allN_iff _ _).1 ((allN_iff _ _).1 q5 j hj) j' hj'
    rw [Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [allLt_iff]
      intro e he
      have h2 := (allN_iff _ _).1 h e he
      rw [hLX j hj, hLX j' hj', pow_eq (pLX j' hj'),
        eqA_unpack' hw (pLX j hj) (pPw (pLX j' hj') e)]
      exact h2
  · rw [allLt_iff]
    intro j hj
    have h := (allN_iff _ _).1 q6 j hj
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨hv, h5⟩, hn⟩, hm⟩ := h
    rw [hLX j hj]
    refine ⟨⟨⟨validA_unpack hv, ?_⟩, ?_⟩, ?_⟩
    · rw [pow_eq (pLX j hj), hI, eqA_unpack' hw (pPw (pLX j hj) 5) pI]
      exact h5
    · rw [hI, eqA_unpack' hw (pLX j hj) pI]
      exact hn
    · rw [any_eqA_unpack' hw bQ.1 bQ.2.1 pQ (pLX j hj)]
      exact hm
  · rw [allLt_iff]
    intro k hk
    have h := (allN_iff _ _).1 q7 k hk
    rw [Bool.and_eq_true] at h
    rw [hQG k hk]
    exact inP_of h.1 (range_of_permOK (pQG k hk)) h.2
  · rw [hQG 0 (by norm_num), hQG 1 (by norm_num)]
    exact comm_of (pQG 0 (by norm_num)) (pQG 1 (by norm_num)) (by quickRfl)

end CertificateChecks.KernelMisc.J2F

end

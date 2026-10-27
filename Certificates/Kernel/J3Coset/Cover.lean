module

public import Certificates.Kernel.J3Coset.Prim
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverGroup
import Certificates.Kernel.J3Coset.ChecksSmall

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.J3C CFSG.KD.J3C CFSG.KS MulAction CFSG.AGLEmbedding.KFactProofs.J3Cover

theorem cov_facts : baseEq tb beta0 (rep 3 xW) [] = true ∧ (!baseEq tb beta0 xW []) = true ∧
    baseEq tb beta0 (d1W ++ xW) (xW ++ d1W) = true ∧ baseEq tb beta0 (d2W ++ xW) (xW ++ d2W) = true ∧
    baseEq tb beta0 (gW ++ xW) (invW xW ++ gW) = true ∧ baseEq tb beta0 (rep 2 d1W) [] = true ∧
    baseEq tb beta0 (rep 4 d2W) [] = true ∧ baseEq tb beta0 (rep 5 (d1W ++ d2W)) [] = true ∧
    baseEq tb beta0 (rep 5 (d1W ++ rep 2 d2W)) [] = true ∧
    (uW == d1W ++ d2W ++ d1W ++ d2W ++ d2W ++ d1W ++ d2W ++ d2W ++ d2W) = true ∧
    baseEq tb beta0 (rep 3 uW) [] = true ∧ (!baseEq tb beta0 uW []) = true ∧
    (!baseEq tb beta0 uW xW) = true ∧ (!baseEq tb beta0 uW (rep 2 xW)) = true ∧
    baseEq tb beta0 (d1W ++ uW) (invW uW ++ d1W) = true ∧
    [xW, d1W, d2W, gW].all codesAB = true := by
  have h := cov_ok
  unfold covChk at h
  simp only [Bool.and_eq_true, and_assoc] at h
  exact h

section Cover

variable {J : Type} [Group J] [Finite J] [MulAction J (Fin nn)] {g : ℕ → J}

variable (hg : Acts g)
include hg

theorem word_ne' (w v : List ℕ) (hw : ∀ c ∈ w, c < 8) (hv : ∀ c ∈ v, c < 8)
    (h : (!baseEq tb beta0 w v) = true) : ev g w ≠ ev g v := by
  intro e
  have h0 : wv tb w 0 = wv tb v 0 := by
    have a := ev_smul hg hw pt0
    have b := ev_smul hg hv pt0
    rw [e] at a
    exact a.symm.trans b
  have h1 : wv tb w beta0 = wv tb v beta0 := by
    have a := ev_smul hg hw ptB
    have b := ev_smul hg hv ptB
    rw [e] at a
    exact a.symm.trans b
  rw [baseEq_of h0 h1] at h
  exact absurd h (by decide)

theorem coverData (hJ : Nat.card J = 50232960) :
    CoverData (ev g xW) (ev g d1W) (ev g d2W) (ev g gW) (ev g uW) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := cov_facts
  have hcodes : ∀ w ∈ [xW, d1W, d2W, gW], ∀ c ∈ w, c < 8 := fun w hw =>
    codesAB_lt (List.all_eq_true.1 h16 w hw)
  have cx := hcodes xW (by simp)
  have c1 := hcodes d1W (by simp)
  have c2 := hcodes d2W (by simp)
  have cg := hcodes gW (by simp)
  have hu : uW = d1W ++ d2W ++ d1W ++ d2W ++ d2W ++ d1W ++ d2W ++ d2W ++ d2W := eq_of_beq h10
  have cu : ∀ c ∈ uW, c < 8 := by
    rw [hu]
    intro c hc
    simp only [List.mem_append, or_assoc] at hc
    rcases hc with h | h | h | h | h | h | h | h | h
    all_goals first | exact c1 c h | exact c2 c h
  have hxAB : codesAB xW = true := List.all_eq_true.1 h16 xW (by simp)
  have huAB : codesAB uW = true := by
    unfold codesAB
    rw [List.all_eq_true]
    intro c hc
    have := cu c hc
    rw [hu] at hc
    simp only [List.mem_append, or_assoc] at hc
    have hd1 : codesAB d1W = true := List.all_eq_true.1 h16 d1W (by simp)
    have hd2 : codesAB d2W = true := List.all_eq_true.1 h16 d2W (by simp)
    unfold codesAB at hd1 hd2
    rw [List.all_eq_true] at hd1 hd2
    rcases hc with h | h | h | h | h | h | h | h | h
    all_goals first | exact hd1 c h | exact hd2 c h
  have hinvx := ev_invW hg hJ hxAB
  have hinvu := ev_invW hg hJ huAB
  have cix := codesAB_lt (invW_codes hxAB)
  have ciu := codesAB_lt (invW_codes huAB)
  refine
    { x_cube := ?_, x_ne := ?_, comm₁ := ?_, comm₂ := ?_, inv_x := ?_, rel₁ := ?_, rel₂ := ?_,
      rel₃ := ?_, rel₄ := ?_, u_mem := ?_, u_cube := ?_, u_ne_one := ?_, u_ne_x := ?_,
      u_ne_x_sq := ?_, inv_u := ?_ }
  · have := word_eq hJ hg _ [] (rep_codes cx 3) (by decide) h1
    rwa [ev_rep, ev_nil] at this
  · exact word_ne' hg xW [] cx (by decide) h2
  · have := word_eq hJ hg _ _ (codes_app c1 cx) (codes_app cx c1) h3
    rwa [ev_append, ev_append] at this
  · have := word_eq hJ hg _ _ (codes_app c2 cx) (codes_app cx c2) h4
    rwa [ev_append, ev_append] at this
  · have := word_eq hJ hg _ _ (codes_app cg cx) (codes_app cix cg) h5
    rw [ev_append, ev_append, hinvx] at this
    rw [this]
    group
  · have := word_eq hJ hg _ [] (rep_codes c1 2) (by decide) h6
    rwa [ev_rep, ev_nil] at this
  · have := word_eq hJ hg _ [] (rep_codes c2 4) (by decide) h7
    rwa [ev_rep, ev_nil] at this
  · have := word_eq hJ hg _ [] (rep_codes (codes_app c1 c2) 5) (by decide) h8
    rwa [ev_rep, ev_append, ev_nil] at this
  · have := word_eq hJ hg _ [] (rep_codes (codes_app c1 (rep_codes c2 2)) 5) (by decide) h9
    rwa [ev_rep, ev_append, ev_rep, ev_nil] at this
  · have m1 : ev g d1W ∈ Subgroup.closure ({ev g d1W, ev g d2W} : Set J) :=
      Subgroup.subset_closure (by simp)
    have m2 : ev g d2W ∈ Subgroup.closure ({ev g d1W, ev g d2W} : Set J) :=
      Subgroup.subset_closure (by simp)
    have e : ev g uW = [ev g d1W, ev g d2W, ev g d1W, ev g d2W, ev g d2W, ev g d1W, ev g d2W,
        ev g d2W, ev g d2W].prod := by
      rw [hu]
      simp only [ev_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [e]
    apply Subgroup.list_prod_mem
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h <;> rw [h]
    all_goals first | exact m1 | exact m2
  · have := word_eq hJ hg _ [] (rep_codes cu 3) (by decide) h11
    rwa [ev_rep, ev_nil] at this
  · exact word_ne' hg uW [] cu (by decide) h12
  · exact word_ne' hg uW xW cu cx h13
  · have := word_ne' hg uW (rep 2 xW) cu (rep_codes cx 2) h14
    rwa [ev_rep] at this
  · have := word_eq hJ hg _ _ (codes_app c1 cu) (codes_app ciu c1) h15
    rw [ev_append, ev_append, hinvu] at this
    rw [this]
    group

end Cover

end CertificateChecks.KernelJ3C

end

module

public import Certificates.Kernel.Sporadic.Fi22.Small17335K
public import Certificates.Kernel.Sporadic.Fi22.Five8124G

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Small17335

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fv8124
open CFSG.Monster.B.Fischer (fi22P)

@[expose] noncomputable def cntR (T : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
    (fun x acc => Nat.add acc (nIf(Nat.beq (T x) x, nat_lit 1, nat_lit 0))) n

theorem cntR_succ (T : ℕ → ℕ) (n : ℕ) :
    cntR T (n + 1) = cntR T n + if T n = n then 1 else 0 := by
  change Nat.add (cntR T n) (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (T n) n)) = _
  cases h : Nat.beq (T n) n
  · have hne : T n ≠ n := fun e => by
      rw [e, Nat.beq_refl] at h
      exact Bool.noConfusion h
    rw [if_neg hne]
    rfl
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]
    rfl

theorem cntR_eq_card (T : ℕ → ℕ) (n : ℕ) : cntR T n = Nat.card {x : Fin n // T x = x} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fin.sum_univ_eq_sum_range (fun i => if T i = i then 1 else 0) n]
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih, cntR_succ]

theorem card_fix_pe {p : ℕ} (hp : PP 3510 12 p) :
    Nat.card {w : Fin 3510 // pe p w = w} = cntP p := by
  change _ = cntR (ev p) 3510
  rw [cntR_eq_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [← pe_apply hp]
  exact ⟨fun e => congrArg Fin.val e, Fin.ext⟩

theorem u_facts {u q f : ℕ}
    [Fact q.Prime] (h : chkU u q f = true) :
    ∃ g ∈ fi22P, orderOf g = q ∧ Nat.card {w : Fin 3510 // g w = w} = f := by
  unfold chkU at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hp, hs⟩, hq⟩, h1⟩, hf⟩ := h
  have pU := PP_of_isP hp
  refine ⟨pe u, (mem_P pU).2 hs, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [← pe_pw pU, ← pe_id]
    exact (pe_eq_iff (PP_pw pU q) PP_id).2 hq
  · rw [← pe_id]
    exact ne_of pU PP_id h1
  · rw [card_fix_pe pU]
    exact Nat.eq_of_beq_eq_true hf

theorem facts :
    (∃ u ∈ fi22P, orderOf u = 7 ∧ Nat.card {w : Fin 3510 // u w = w} = 3) ∧
      (∃ u ∈ fi22P, orderOf u = 11 ∧ Nat.card {w : Fin 3510 // u w = w} = 1) ∧
      (∃ u ∈ fi22P, orderOf u = 13 ∧ Nat.card {w : Fin 3510 // u w = w} = 0) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h7 := ok7
  have h11 := ok11
  have h13 := ok13
  rw [Fv8124.strictB_eq] at h7 h11 h13
  exact ⟨u_facts h7, u_facts h11, u_facts h13⟩

end CertificateChecks.KernelSpor.Small17335

end

module

public import CFSG.Certificates.Kernel.Spor.Loops
public import Certificates.Data.Kernel.Spor.TextAt

public section

namespace CertificateChecks.KernelMisc.TextBlocks

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text

@[expose] noncomputable def scanK (k : Nat) : List Char → Option (List Char) :=
  Nat.rec (motive := fun _ => List Char → Option (List Char)) (fun cs => some cs)
    (fun _ ih cs => List.rec (motive := fun _ => Option (List Char)) none
      (fun c t _ => Bool.rec (motive := fun _ => Option (List Char)) none (ih t)
        (Nat.blt (Char.toNat c) (nat_lit 128))) cs) k

@[expose] noncomputable def asciiBlocks (n K : Nat) : List Char → Bool :=
  Nat.rec (motive := fun _ => List Char → Bool) (fun _ => true)
    (fun _ ih cs => Option.rec (motive := fun _ => Bool) false (fun r => ih r) (scanK K cs)) n

theorem scanK_spec {k : Nat} {cs r : List Char} (h : scanK k cs = some r) :
    asciiK (cs.take k) = true ∧ cs.drop k = r := by
  induction k generalizing cs with
  | zero =>
    change some cs = some r at h
    exact ⟨rfl, Option.some.inj h⟩
  | succ k ih =>
    cases cs with
    | nil => exact absurd h (by simp [scanK])
    | cons c t =>
      change Bool.rec (motive := fun _ => Option (List Char)) none (scanK k t)
        (Nat.blt (Char.toNat c) (nat_lit 128)) = some r at h
      cases hc : Nat.blt (Char.toNat c) (nat_lit 128)
      · rw [hc] at h
        exact absurd h (by simp)
      · rw [hc] at h
        obtain ⟨h1, h2⟩ := ih h
        refine ⟨?_, h2⟩
        change bAnd(Nat.blt (Char.toNat c) (nat_lit 128), asciiK (t.take k)) = true
        rw [hc, h1]

theorem asciiK_iff {cs : List Char} : asciiK cs = true ↔ ∀ c ∈ cs, c.toNat < 128 := by
  induction cs with
  | nil => exact ⟨fun _ c hc => absurd hc List.not_mem_nil, fun _ => rfl⟩
  | cons c t ih =>
    change bAnd(Nat.blt (Char.toNat c) (nat_lit 128), asciiK t) = true ↔ _
    rw [bAnd_iff, ih, Nat.blt_eq, List.forall_mem_cons]

theorem asciiBlocks_spec {n K : Nat} {cs : List Char} (h : asciiBlocks n K cs = true) :
    asciiK (cs.take (n * K)) = true := by
  induction n generalizing cs with
  | zero =>
    rw [Nat.zero_mul, List.take_zero]
    rfl
  | succ n ih =>
    change Option.rec (motive := fun _ => Bool) false (fun r => asciiBlocks n K r) (scanK K cs) =
      true at h
    cases hs : scanK K cs with
    | none =>
      rw [hs] at h
      exact absurd h (by simp)
    | some r =>
      rw [hs] at h
      obtain ⟨h1, h2⟩ := scanK_spec hs
      have h3 := ih h
      rw [← h2] at h3
      rw [Nat.succ_mul, Nat.add_comm, List.take_add, asciiK_iff, List.forall_mem_append]
      exact ⟨asciiK_iff.1 h1, asciiK_iff.1 h3⟩

theorem asciiK_take {cs : List Char} {a b : Nat} (hab : a ≤ b) (h : asciiK (cs.take b) = true) :
    asciiK (cs.take a) = true := by
  rw [asciiK_iff] at h ⊢
  intro c hc
  refine h c ?_
  have e : cs.take a = (cs.take b).take a := by rw [List.take_take, Nat.min_eq_left hab]
  rw [e] at hc
  exact List.mem_of_mem_take hc

end CertificateChecks.KernelMisc.TextBlocks

end

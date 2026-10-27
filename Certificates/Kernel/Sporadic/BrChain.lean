module

public section

namespace CertificateChecks.KernelSpor.BrChain

@[expose] def segs (W : Nat → List Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => segs W n ++ W n

theorem run_chain {run : List Nat → Nat → Nat} (hnil : ∀ s, run [] s = s)
    (happ : ∀ l₁ l₂ s, run (l₁ ++ l₂) s = run l₂ (run l₁ s)) (W : Nat → List Nat)
    (St : Nat → Nat) : ∀ n, (∀ k < n, Nat.beq (run (W k) (St k)) (St (k + 1)) = true) →
      Nat.beq (run (segs W n) (St 0)) (St n) = true
  | 0, _ => by
    change Nat.beq (run [] (St 0)) (St 0) = true
    rw [hnil, Nat.beq_eq]
  | n + 1, h => by
    have ih := run_chain hnil happ W St n (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have hn := h n (Nat.lt_succ_self n)
    rw [Nat.beq_eq] at ih hn ⊢
    change run (segs W n ++ W n) (St 0) = St (n + 1)
    rw [happ, ih, hn]

theorem run_chain_to {run : List Nat → Nat → Nat} (hnil : ∀ s, run [] s = s)
    (happ : ∀ l₁ l₂ s, run (l₁ ++ l₂) s = run l₂ (run l₁ s)) (W : Nat → List Nat)
    (St : Nat → Nat) (n s₀ s : Nat) (h₀ : St 0 = s₀) (hs : St n = s)
    (h : ∀ k < n, Nat.beq (run (W k) (St k)) (St (k + 1)) = true) :
    Nat.beq (run (segs W n) s₀) s = true := by
  subst h₀ hs
  exact run_chain hnil happ W St n h

end CertificateChecks.KernelSpor.BrChain

end

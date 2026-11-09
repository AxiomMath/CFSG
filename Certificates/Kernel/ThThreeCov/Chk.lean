module

public import Certificates.Data.Kernel.ThThreeCov.Defs
public import Certificates.Kernel.ThThreeCov.Data
public import Certificates.Kernel.Th.Fam.K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Each

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelThThreeCov

open CFSG.KC.Th CFSG.KC.ThThreeCov CFSG.KD.ThThreeCov CertificateChecks.KernelTh.Fam

theorem ch1023506L : andB (Nat.beq (lenR defs) 221) (Nat.beq (lenR cls) 3) = true := by quickRfl

theorem ch1023506S : seedsOK thK RB = true := by quickRfl

@[expose] noncomputable def ch1023506D (c : Nat) : Bool := defsChunk thK RB defs c

#kc_each ch1023506D 0 11
#kc_each ch1023506D 12 14

@[expose] noncomputable def dStep (k : CFSG.KC.Th.Expr.K) (R : Nat → Nat) (D : List (List Nat))
    (c i : Nat) : Bool :=
  Bool.rec true (defOK k R (16 * c + i) (D.getD (16 * c + i) [])) (Nat.blt (16 * c + i) (lenR D))

@[expose] noncomputable def defsRun (k : CFSG.KC.Th.Expr.K) (R : Nat → Nat) (D : List (List Nat))
    (c lo n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc (dStep k R D c (lo + j))) n

theorem andB_eq_true_iff' {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem andB_rec_iff (f : Nat → Bool) (n : Nat) :
    Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc (f j)) n = true ↔
      ∀ j < n, f j = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    show andB (Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc (f j)) n) (f n) = true ↔
      _
    rw [andB_eq_true_iff', ih]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · exact h1 j h
      · exact h2
    · intro h
      exact ⟨fun j hj => h j (by omega), h n (by omega)⟩

theorem defsChunk_of_halves {k : CFSG.KC.Th.Expr.K} {R : Nat → Nat} {D : List (List Nat)}
    {c : Nat}
    (h1 : defsRun k R D c 0 8 = true) (h2 : defsRun k R D c 8 8 = true) :
    defsChunk k R D c = true := by
  have e : defsChunk k R D c =
      Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc (dStep k R D c j)) 16 := rfl
  rw [e, andB_rec_iff]
  rw [defsRun, andB_rec_iff] at h1 h2
  intro j hj
  rcases Nat.lt_or_ge j 8 with h | h
  · have h' := h1 j h
    rwa [Nat.zero_add] at h'
  · have h' := h2 (j - 8) (by omega)
    rwa [Nat.add_sub_cancel' h] at h'

theorem ch1023506D11a : defsRun thK RB defs 11 0 8 = true := by quickRfl
theorem ch1023506D11b : defsRun thK RB defs 11 8 8 = true := by quickRfl
theorem ch1023506D11 : ch1023506D (nat_lit 11) = true :=
  defsChunk_of_halves (k := thK) (R := RB) (D := defs) (c := 11) ch1023506D11a ch1023506D11b


theorem ch1023506G : tabGlobal thK RB (5 + lenR defs) tb g1 g2 ord = true := by quickRfl

@[expose] noncomputable def ch1023506T (j : Nat) : Bool :=
  tabRow thK RB tb g1 g2 kv tpar tgen cl ord j

#kc_each ch1023506T 0 81

theorem ch1023506I : invsOK thK RB (5 + lenR defs) invs = true := by quickRfl

@[expose] noncomputable def ch1023506C (i : Nat) : Bool :=
  clsOK thK RB (5 + lenR defs) tb invs (cls.getD i (0, [], [], []))

#kc_each ch1023506C 0 3

end CertificateChecks.KernelThThreeCov

end

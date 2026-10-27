
module

public import Certificates.Kernel.Fi23M.KeysBase
import Certificates.Kernel.Fi23M.TreeK
import Certificates.Kernel.Fi23K.OrbEq
import CFSG.Certificates.Kernel.Spor.PChainSound
import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelFi23M

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.KD.Fi23K CFSG.KC.Fi23K CFSG.KC.Enum
  CFSG.Sporadic.Th.Native CFSG.KS.Raw.Orb

theorem foldl_indexW (keys : Array (Array W))
    (hinj : ∀ i < keys.size, ∀ j < keys.size, keys[i]! = keys[j]! → i = j) (d : Nat) :
    ∀ n ≤ keys.size, ∀ k < n,
      ((List.range n).foldl (fun m i => m.insert keys[i]! i)
        (∅ : Std.HashMap (Array W) Nat)).getD keys[k]! d = k := by
  intro n
  induction n with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro hn k hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Std.HashMap.getD_insert]
    by_cases hkn : k = n
    · subst hkn
      simp
    · have hne : (keys[n]! == keys[k]!) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hkn (hinj n (by omega) k (by omega) e).symm
      rw [hne]
      exact ih (by omega) k (by omega)

theorem indexOfW_getD {keys : Array (Array W)}
    (hinj : ∀ i < keys.size, ∀ j < keys.size, keys[i]! = keys[j]! → i = j) {k : Nat}
    (hk : k < keys.size) : (indexOfW keys).getD keys[k]! keys.size = k :=
  foldl_indexW keys hinj keys.size keys.size (Nat.le_refl _) k hk

theorem eqW_self_of {X : Array W} (h : X.size = 253) : eqW 253 X X = true := by
  unfold eqW
  simp [h]

theorem tree_pt {k : ℕ} (hk : k < 31671) (hk0 : k ≠ 0) : tb G 91 k < k ∧
    ((tb G 92 k = 1 ∧ tb G 39 (tb G 91 k) = k) ∨ (tb G 92 k = 2 ∧ tb G 40 (tb G 91 k) = k)) := by
  have h0 := tree_ok
  unfold CFSG.KD.Fi23K.trK at h0
  have h := allN_iff.1 h0 k hk
  unfold CFSG.KD.Fi23K.trAt at h
  have hb : k.beq 0 = false := by
    cases e : k.beq 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hk0
  rw [bIf_eq, hb, if_neg Bool.false_ne_true, strictB_eq, bAnd_eq, Bool.and_eq_true, bIf_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, ?_⟩
  cases e : Nat.beq (tb G 92 k) 1
  · rw [e, if_neg Bool.false_ne_true, bAnd_eq, Bool.and_eq_true] at h2
    exact Or.inr ⟨Nat.eq_of_beq_eq_true h2.1, Nat.eq_of_beq_eq_true h2.2⟩
  · rw [e, if_pos rfl] at h2
    exact Or.inl ⟨Nat.eq_of_beq_eq_true e, Nat.eq_of_beq_eq_true h2⟩

theorem tree_conj {k : ℕ} (hk : k < 31671) : (k == 0 || (decide (ap orbLit.par k < k) &&
    ((ap orbLit.lab k == 1 && ap orbLit.alpha (ap orbLit.par k) == k) ||
      (ap orbLit.lab k == 2 && ap orbLit.beta (ap orbLit.par k) == k)))) = true := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rfl
  obtain ⟨hp, hl⟩ := tree_pt hk (by omega)
  have ep : ap orbLit.par k = tb G 91 k := ap_tabOf 91 hk
  have el : ap orbLit.lab k = tb G 92 k := ap_tabOf 92 hk
  have ea : ap orbLit.alpha (tb G 91 k) = tb G 39 (tb G 91 k) := ap_tabOf 39 (by omega)
  have eb : ap orbLit.beta (tb G 91 k) = tb G 40 (tb G 91 k) := ap_tabOf 40 (by omega)
  rw [ep, el, ea, eb]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact Or.inr ⟨hp, hl⟩

end CertificateChecks.KernelFi23M

end

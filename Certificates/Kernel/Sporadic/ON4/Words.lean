
module

public import Certificates.Kernel.Sporadic.ON3.Strong
public import Certificates.Kernel.Sporadic.ON4.WordsData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.ONSchreier CFSG.KS.TW CFSG.KS.Words CertificateChecks.KernelSpor.ON3

@[expose] def wordL4 : List (List Int) :=
  [Data.McommChain.strongWords[3]!, Data.McommChain.strongWords[4]!,
    Data.LcommChain.strongWords[3]!, Data.LcommChain.strongWords[4]!,
    Data.LcommChain.strongWords[5]!, Data.jointChain.strongWords[6]!,
    Data.jointChain.strongWords[7]!, Data.jointChain.strongWords[8]!]

theorem words4_dec : ((List.range 8).all fun k =>
    decide (decW (ON4W.WC k) (ON4W.WL k) = wordL4.getD k []) &&
      decide (decW (ON4W.WC (k + 8)) (ON4W.WL (k + 8)) = invW (wordL4.getD k []))) = true := by
  decide +kernel

theorem dec4_eq {k : Nat} (hk : k < 8) : decW (ON4W.WC k) (ON4W.WL k) = wordL4.getD k [] := by
  have h := List.all_eq_true.1 words4_dec k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem dec4_inv {k : Nat} (hk : k < 8) :
    decW (ON4W.WC (k + 8)) (ON4W.WL (k + 8)) = invW (wordL4.getD k []) := by
  have h := List.all_eq_true.1 words4_dec k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem tr4_word (G GI : Nat → Nat → Nat) {k : Nat} (hk : k < 8) (x : Nat) :
    CFSG.KS.ON.trace G GI (ON4W.WC k) (ON4W.WL k) x = (wordL4.getD k []).foldr (GZ G GI) x := by
  rw [trace_eq, dec4_eq hk]

theorem tr4_inv (G GI : Nat → Nat → Nat) {k : Nat} (hk : k < 8) (x : Nat) :
    CFSG.KS.ON.trace G GI (ON4W.WC (k + 8)) (ON4W.WL (k + 8)) x =
      (invW (wordL4.getD k [])).foldr (GZ G GI) x := by
  rw [trace_eq, dec4_inv hk]

theorem letters4 : ((wordL4.getD 0 []).all fun l => l != 0 && decide (l.natAbs ≤ 3)) &&
    ((wordL4.getD 1 []).all fun l => l != 0 && decide (l.natAbs ≤ 4)) &&
    ((wordL4.getD 2 []).all fun l => l != 0 && decide (l.natAbs ≤ 3)) &&
    ((wordL4.getD 3 []).all fun l => l != 0 && decide (l.natAbs ≤ 4)) &&
    ((wordL4.getD 4 []).all fun l => l != 0 && decide (l.natAbs ≤ 5)) &&
    ((wordL4.getD 5 []).all fun l => l != 0 && decide (l.natAbs ≤ 6)) &&
    ((wordL4.getD 6 []).all fun l => l != 0 && decide (l.natAbs ≤ 7)) &&
    ((wordL4.getD 7 []).all fun l => l != 0 && decide (l.natAbs ≤ 8)) = true := by
  decide +kernel

theorem lets4 : LetM 3 (wordL4.getD 0 []) ∧ LetM 4 (wordL4.getD 1 []) ∧
    LetM 3 (wordL4.getD 2 []) ∧ LetM 4 (wordL4.getD 3 []) ∧ LetM 5 (wordL4.getD 4 []) ∧
    LetM 6 (wordL4.getD 5 []) ∧ LetM 7 (wordL4.getD 6 []) ∧ LetM 8 (wordL4.getD 7 []) := by
  have h := letters4
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨letM_of h1, letM_of h2, letM_of h3, letM_of h4, letM_of h5, letM_of h6, letM_of h7,
    letM_of h8⟩

end CertificateChecks.KernelSpor.ON4K

end

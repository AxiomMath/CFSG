module

public import Certificates.Kernel.SchreierFam.C188002F

public section

namespace CertificateChecks.KernelSchreierFam.U38

open CFSG.RankThree.PartTwo.Sec4.Item434U38 GF64

theorem eq_iff {a b : GF64} : a = b ↔ a.toNat = b.toNat := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  simp [GF64.toNat, Fin.ext_iff]

theorem ofNat'_eq {m m' : Nat} (h : m % 64 = m' % 64) : ofNat' m = ofNat' m' :=
  eq_iff.2 h

theorem mem (a : GF64) : a.toNat ∈ List.range 64 := List.mem_range.2 a.val.2

theorem all3 {p : Nat → Nat → Nat → Bool}
    (h : (List.range 64).all (fun x => (List.range 64).all fun y => (List.range 64).all
      fun z => p x y z) = true) (a b c : GF64) : p a.toNat b.toNat c.toNat = true :=
  List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 h _ (mem a)) _ (mem b)) _ (mem c)

theorem field :
    (∀ a b c : GF64, a + b + c = a + (b + c)) ∧ (∀ a : GF64, 0 + a = a) ∧
      (∀ a : GF64, -a + a = 0) ∧ (∀ a b c : GF64, a * b * c = a * (b * c)) ∧
      (∀ a b : GF64, a * b = b * a) ∧ (∀ a : GF64, 1 * a = a) ∧
      (∀ a : GF64, a ≠ 0 → a * a⁻¹ = 1) ∧ ((0 : GF64)⁻¹ = 0) ∧
      (∀ a b c : GF64, a * (b + c) = a * b + a * c) ∧ (∃ a b : GF64, a ≠ b) := by
  obtain ⟨h0, hn, hc, h1, hi, hz, he⟩ := small
  refine ⟨fun a b c => ofNat'_eq (beq_iff_eq.1 (all3 nAddAssoc a b c)), h0, hn,
    fun a b c => ofNat'_eq (beq_iff_eq.1 (all3 nMulAssoc a b c)), hc, h1, hi, hz,
    fun a b c => ofNat'_eq (beq_iff_eq.1 (all3 nDistrib a b c)), he⟩

end CertificateChecks.KernelSchreierFam.U38

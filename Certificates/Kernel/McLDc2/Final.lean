module

public import Certificates.Kernel.McLDc2.Glob
public import Certificates.Kernel.McLDc2.Rec2
public import Certificates.Kernel.McLDc2.R0
public import Certificates.Kernel.McLDc2.R1
public import Certificates.Kernel.McLDc2.R2
public import Certificates.Kernel.McLDc2.R3

public section

namespace CFSG.KD.McLDc2

open CFSG.KC.SLD2 CFSG.KC.Co3Bfs CFSG.Sporadic.Schreier

theorem of_off {P f : Nat → Bool} {o c : Nat} (hf : ∀ i, f i = P (Nat.add o i))
    (h : ∀ i < c, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + c) : P i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem rec2s : (List.range D.R1.length).all (rec2OK C D) = true := by
  rw [Nat.eq_of_beq_eq_true nR1, List.all_eq_true]
  intro c hc
  exact cover_of_blocks (B := 16) (nb := 19) (by omega) (by decide) R2B.all c
    (List.mem_range.1 hc)

theorem roots_ok : (List.range D.roots.length).all (rootsOK C D) = true := by
  rw [Nat.eq_of_beq_eq_true nroots, List.all_eq_true]
  intro b hb
  rw [List.mem_range] at hb
  have h0 := cover_of_blocks (B := 5) (nb := 15) (by omega) (by decide) RB0.all
  have h1 := cover_of_blocks (B := 5) (nb := 15) (by omega) (by decide) RB1.all
  have h2 := cover_of_blocks (B := 5) (nb := 14) (by omega) (by decide) RB2.all
  have h3 := cover_of_blocks (B := 5) (nb := 14) (by omega) (by decide) RB3.all
  by_cases c0 : b < 75
  · exact of_off (o := 0) (fun _ => rfl) h0 (by omega) (by omega)
  by_cases c1 : b < 150
  · exact of_off (o := 75) (fun _ => rfl) h1 (by omega) (by omega)
  by_cases c2 : b < 220
  · exact of_off (o := 150) (fun _ => rfl) h2 (by omega) (by omega)
  · exact of_off (o := 220) (fun _ => rfl) h3 (by omega) (by omega)

theorem dc_ok : dc2Check C D = true := by
  unfold dc2Check
  rw [glob, borbs, rec1s, frest, frows, rec2s, roots_ok, rootIdx]
  rfl

theorem lc_eq {l : Nat} (hl : l < 2) :
    LT.lc.getD (Nat.add 5 l) 0 = CertificateChecks.KernelMisc.HSMcL.MS.F l := by
  have h := codes
  rw [Bool.and_eq_true] at h
  interval_cases l
  · exact Nat.eq_of_beq_eq_true h.1
  · exact Nat.eq_of_beq_eq_true h.2

theorem ab_eq : ∀ l < 2, ∀ p < 275, (mclStrongArrs[l]!)[p]! = L (Nat.add 5 l) p := by
  intro l hl p hp
  rw [CertificateChecks.KernelMisc.HSMcL.mclStrongArrs_get l hl,
    getElem!_pos _ p (by simpa [CFSG.KS.Raw.unpack] using hp)]
  simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn]
  unfold L
  rw [lc_eq hl]
  rfl

theorem sep_eq : D.sep = [0, 1, 2, 3, 4] :=
  eq_of_beq sepB

theorem sb_size : SB.C.flatten.length = 128 :=
  eq_of_beq sbSize

open Certificates in
open CFSG.KD.McLDc2 in
theorem facts :
    CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 275, (CFSG.Sporadic.Schreier.mclStrongArrs[l]!)[p]! = L (Nat.add 5 l) p) ∧
    shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 3, 4] ∧ sbOK = true ∧
    SB.C.flatten.length = 128 :=
  ⟨dc_ok, ab_eq, shape, lets, sep_eq, sb, sb_size⟩

end CFSG.KD.McLDc2

end

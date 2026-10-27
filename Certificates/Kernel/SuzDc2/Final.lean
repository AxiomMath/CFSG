module

public import Certificates.Kernel.SuzDc2.Glob
public import Certificates.Kernel.SuzDc2.Rec1A
public import Certificates.Kernel.SuzDc2.Rec1B
public import Certificates.Kernel.SuzDc2.Rec1C
public import Certificates.Kernel.SuzDc2.Rec1D
public import Certificates.Kernel.SuzDc2.S0
public import Certificates.Kernel.SuzDc2.S1
public import Certificates.Kernel.SuzDc2.S2
public import Certificates.Kernel.SuzDc2.S3
public import Certificates.Kernel.SuzDc2.S4
public import Certificates.Kernel.SuzDc2.ST
public import Certificates.Kernel.SuzDc2.W0
public import Certificates.Kernel.SuzDc2.W1
public import Certificates.Kernel.SuzDc2.W2
public import Certificates.Kernel.SuzDc2.W3
public import Certificates.Kernel.SuzDc2.WH
public import CFSG.Certificates.Kernel.SporLatDcSortSplit

public section

namespace CFSG.KD.SuzDc2

open CFSG.KC.SLD2 CFSG.KC.SLDc CFSG.KC.Co3Bfs

private theorem of_off {P f : Nat → Bool} {o c : Nat} (hf : ∀ i, f i = P (Nat.add o i))
    (h : ∀ i < c, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + c) : P i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem borbs : (List.range D.bo.length).all (fun i => borbOK C D (D.bo.getD i default)) =
    true := by
  rw [Nat.eq_of_beq_eq_true nbo, List.all_eq_true]
  intro i hi
  exact cover_of_blocks (B := 1) (nb := 4) (by omega) (by decide) BOB.all i (List.mem_range.1 hi)

theorem rec1s : (List.range D.R1.length).all (fun c => rec1OK C D (D.R1.getD c default)) =
    true := by
  rw [Nat.eq_of_beq_eq_true nR1, List.all_eq_true]
  intro c hc
  rw [List.mem_range] at hc
  have hA := cover_of_blocks (B := 1) (nb := 25) (by omega) (by decide) R1A.all
  have hB := cover_of_blocks (B := 1) (nb := 20) (by omega) (by decide) R1B.all
  have hC := cover_of_blocks (B := 1) (nb := 30) (by omega) (by decide) R1C.all
  have hD := cover_of_blocks (B := 1) (nb := 31) (by omega) (by decide) R1D.all
  have off := @of_off (fun c => rec1OK C D (D.R1.getD c default))
  by_cases c0 : c < 25
  · exact off (o := 0) (fun _ => rfl) hA (by omega) (by omega)
  by_cases c1 : c < 45
  · exact off (o := 25) (fun _ => rfl) hB (by omega) (by omega)
  by_cases c2 : c < 75
  · exact off (o := 45) (fun _ => rfl) hC (by omega) (by omega)
  · exact off (o := 75) (fun _ => rfl) hD (by omega) (by omega)

theorem frows : (List.range C.nf).all (fRowOK C D) = true := by
  rw [List.all_eq_true]
  intro i hi
  exact cover_of_blocks (B := 1) (nb := 6) (by omega) (by decide) FRB.all i (List.mem_range.1 hi)

theorem roots_ok : (List.range D.roots.length).all (rootsOK C D) = true := by
  rw [Nat.eq_of_beq_eq_true nroots, List.all_eq_true]
  intro b hb
  exact cover_of_blocks (B := 5) (nb := 8) (by omega) (by decide) RTB.all b (List.mem_range.1 hb)

theorem dc_ok : dc2Check C D = true := by
  unfold dc2Check
  rw [glob, borbs, rec1s, frest, frows, rec2s, roots_ok, rootIdx]
  rfl

theorem ab_eq : ∀ l < 2, ∀ p < 22880,
    (CFSG.Sporadic.SuzOddCore.certArr l)[p]! = L (Nat.add 6 l) p := by
  intro l hl p hp
  rw [CertificateChecks.KernelSpor.OddCore.certArr_eq (k := l) (by omega),
    CFSG.KS.Row.rowArr_get hp]
  interval_cases l
  · exact Nat.eq_of_beq_eq_true
      (cover_of_blocks (B := 22880) (nb := 1) (by omega) (by decide) CB0.all p hp)
  · exact Nat.eq_of_beq_eq_true
      (cover_of_blocks (B := 22880) (nb := 1) (by omega) (by decide) CB1.all p hp)

theorem wOK_of {l : Nat} {w : List Nat}
    (h : ∀ p < 22880, Nat.beq (L l p) (CFSG.KC.E64F.wordF L w p) = true) : wOK l w = true := by
  unfold wOK
  rw [List.all_eq_true]
  intro p hp
  exact h p (List.mem_range.1 hp)

theorem lets : letOK = true := by
  have hinv : ((List.range 22880).all fun p => Nat.beq (L 4 (L 3 p)) p) = true := by
    rw [List.all_eq_true]
    intro p hp
    exact cover_of_blocks (B := 22880) (nb := 1) (by omega) (by decide) WIB.all p
      (List.mem_range.1 hp)
  unfold letOK
  rw [wOK_of (l := 8) (w := [6, 7])
      (cover_of_blocks (B := 11440) (nb := 2) (by omega) (by decide) WXB.all),
    wOK_of (l := 9) (w := [6, 7, 7])
      (cover_of_blocks (B := 11440) (nb := 2) (by omega) (by decide) WYB.all),
    wOK_of (l := 0) (w := LT.sgw.getD 0 [])
      (cover_of_blocks (B := 2080) (nb := 11) (by omega) (by decide) W0B.all),
    wOK_of (l := 1) (w := LT.sgw.getD 1 [])
      (cover_of_blocks (B := 1907) (nb := 12) (by omega) (by decide) W1B.all),
    wOK_of (l := 2) (w := LT.sgw.getD 2 [])
      (cover_of_blocks (B := 1635) (nb := 14) (by omega) (by decide) W2B.all),
    wOK_of (l := 3) (w := LT.sgw.getD 3 [])
      (cover_of_blocks (B := 1760) (nb := 13) (by omega) (by decide) W3B.all),
    wOK_of (l := 5) (w := LT.hw)
      (cover_of_blocks (B := 4576) (nb := 5) (by omega) (by decide) WHB.all), hinv]
  rfl

theorem sb_size : SB.C.flatten.length = 8192 :=
  eq_of_beq sbSize

theorem sb_ok : sbOK = true := by
  have ho : SB.ord.length = 8192 := by
    have h := sbOrd
    rw [Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, sb_size]
  unfold sbOK
  refine omC_of_parts sbHead (fun l hl => List.all_eq_true.1 sbRowLen l (List.mem_range.2 hl))
    (fun l hl => ?_) sbTreeLen ?_ sbOrd ?_
  · have hl' : l < 5 := hl
    refine all_of_slices (s := 820) (m := 10) (by omega) ?_ ?_
    · rw [List.length_zip, sb_size]
      omega
    · interval_cases l
      · exact cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) RS0.all
      · exact cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) RS1.all
      · exact cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) RS2.all
      · exact cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) RS3.all
      · exact cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) RS4.all
  · refine allIdx_of_slices (s := 820) (m := 10) (by omega) ?_
      (cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) TSB.all)
    rw [List.length_zip, List.length_zip, sb_size]
    omega
  · refine sortedLt_of_slices (s := 820) (m := 10) (by omega) ?_
      (cover_of_blocks (B := 1) (nb := 10) (by omega) (by decide) SSB.all)
    rw [List.length_map, ho]
    omega

open Certificates in
open CFSG.KD.SuzDc2 in
theorem facts :
    CFSG.KC.SLD2.dc2Check C D = true ∧
    (∀ l < 2, ∀ p < 22880, (CFSG.Sporadic.SuzOddCore.certArr l)[p]! = L (Nat.add 6 l) p) ∧
    shapeOK = true ∧ letOK = true ∧ D.sep = [0, 1, 2, 3, 4, 5] ∧ sbOK = true ∧
    SB.C.flatten.length = 8192 :=
  ⟨dc_ok, ab_eq, shape, lets, eq_of_beq sepB, sb_ok, sb_size⟩

end CFSG.KD.SuzDc2

end

module

public import Certificates.Kernel.J3Dc.Glob
public import Certificates.Kernel.J3Dc.G0
public import Certificates.Kernel.J3Dc.G1
public import Certificates.Kernel.J3Dc.G2
public import Certificates.Kernel.J3Dc.G3
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import Certificates.Data.Kernel.J3Dc.Defs
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
import all CFSG.Sporadic.Schreier.PairJ3CertInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.J3Dc

open CFSG.KC.SLDc CFSG.Sporadic.Schreier

theorem ch_of {f : Nat → Bool} {o c : Nat} (hf : ∀ i, f i = chunkOK C D (Nat.add o i))
    (h : ∀ i < c, f i = true) {i : Nat} (h1 : o ≤ i) (h2 : i < o + c) : chunkOK C D i = true := by
  have e : Nat.add o (i - o) = i := by simp only [Nat.add_eq]; omega
  have := h (i - o) (by omega)
  rw [hf, e] at this
  exact this

theorem chunks_ok : (List.range D.Rc.length).all (chunkOK C D) = true := by
  have hl : D.Rc.length = 17 := rfl
  rw [hl, List.all_eq_true]
  intro i hi
  rw [List.mem_range] at hi
  by_cases h0 : i < 4
  · exact ch_of (o := 0) (fun _ => rfl) G0.all (by omega) (by omega)
  by_cases h1 : i < 8
  · exact ch_of (o := 4) (fun _ => rfl) G1.all (by omega) (by omega)
  by_cases h2 : i < 12
  · exact ch_of (o := 8) (fun _ => rfl) G2.all (by omega) (by omega)
  · exact ch_of (o := 12) (fun _ => rfl) G3.all (by omega) (by omega)

theorem dc_ok : dcCheck C D = true := by
  unfold dcCheck
  rw [glob, pts, orbs, chunks_ok]
  rfl

theorem strong_eq {k : Nat} (hk : k < 5) :
    j3StrongArrs[k]! = CFSG.KS.Raw.unpack 6156 13 (CertificateChecks.KernelCensus.J3S.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound CertificateChecks.KernelCensus.J3S.all
  rw [← CertificateChecks.KernelCensus.J3S.eq] at h
  rw [j3StrongArrs, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  exact h k hk

theorem lc_eq {l : Nat} (hl : l < 2) :
    J.lc.getD l 0 = CertificateChecks.KernelCensus.J3S.F l := by
  have h := codes
  rw [Bool.and_eq_true] at h
  interval_cases l
  · exact Nat.eq_of_beq_eq_true h.1
  · exact Nat.eq_of_beq_eq_true h.2

theorem ab_good : ∀ l < 2, (j3StrongArrs[l]!).size = 6156 ∧
    ∀ p < 6156, (j3StrongArrs[l]!).getD p 0 = L l p ∧ L l p < 6156 := by
  intro l hl
  rw [strong_eq (by omega)]
  refine ⟨by simp [CFSG.KS.Raw.unpack], fun p hp => ⟨?_, ?_⟩⟩
  · rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by simpa [CFSG.KS.Raw.unpack] using hp)]
    simp only [CFSG.KS.Raw.unpack, Array.getElem_ofFn, Option.getD_some]
    unfold L
    rw [lc_eq hl]
    rfl
  · have h := ab
    unfold abOK at h
    exact Nat.blt_eq.mp (List.all_eq_true.1 (List.all_eq_true.1 h l (List.mem_range.2 hl)) p
      (List.mem_range.2 hp))

theorem sepB : (D.sep == [0, 1, 3, 2]) = true := by
  quickRfl

theorem omB : ((List.range 5).map (fun j => (Om j).lbl.size) == [1, 3, 3, 9, 15]) = true := by
  quickRfl

theorem sbB : Nat.beq Sb.lbl.size 128 = true := by
  quickRfl

theorem mwB : Nat.beq D.mw.length 5 = true := by
  quickRfl

open Certificates in
open CFSG.KD.J3Dc in
theorem facts :
    CFSG.KC.SLDc.dcCheck C D = true ∧
    (∀ l < 2, (CFSG.Sporadic.Schreier.j3StrongArrs[l]!).size = 6156 ∧
      ∀ p < 6156, (CFSG.Sporadic.Schreier.j3StrongArrs[l]!).getD p 0 = L l p ∧ L l p < 6156) ∧
    sgwOK = true ∧ (∀ i < 3, sgOK i = true) ∧ invOK = true ∧
    D.sep = [0, 1, 3, 2] ∧ D.mw.length = 5 ∧ (List.range 5).all memOK = true ∧
    (List.range 5).map (fun j => (Om j).lbl.size) = [1, 3, 3, 9, 15] ∧
    sbOK = true ∧ Sb.lbl.size = 128 :=
  ⟨dc_ok, ab_good, sgw, fun i hi => by
    interval_cases i
    · exact sg0
    · exact sg1
    · exact sg2, invs, eq_of_beq sepB, Nat.eq_of_beq_eq_true mwB, mems, eq_of_beq omB, sb,
    Nat.eq_of_beq_eq_true sbB⟩

end CFSG.KD.J3Dc

end

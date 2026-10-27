module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClassData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClassData
public import Certificates.Kernel.J4M2.SlpB
public import Certificates.Kernel.J4M2.C12610Checks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.Sporadic.J4Schreier
  CertificateChecks.KernelSporSch.J4E7 CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.KC.J4Slp
  CFSG.Sporadic.GLQ

theorem colK_get (R : List Nat) (o i : Nat) {k : Nat} (hk : k < 27) :
    getN 0 (colK R o i) k = getN 0 R (2 * (o + k) + i) := by
  unfold colK
  rw [slpB_getN, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem colK_get0 (R : List Nat) (o : Nat) {k : Nat} (hk : k < 27) :
    getN 0 (colK R o 0) k = regM R (o + k) := by
  rw [colK_get R o 0 hk]
  rfl

theorem colK_get1 (R : List Nat) (o : Nat) {k : Nat} (hk : k < 27) :
    getN 0 (colK R o 1) k = regI R (o + k) := by
  rw [colK_get R o 1 hk]
  rfl

theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem three_of (R : List Nat) (hR : RegsOK 140 threeRegs R) (h : threeK R = true) :
    threeOK = true := by
  have hK := CertificateChecks.KernelSporSch.J4Real.hK
  unfold threeK at h
  simp only [slpB_forceB_eq] at h
  unfold threeT at h
  obtain ⟨h0, h⟩ := andB_parts h
  obtain ⟨hcl, h⟩ := andB_parts h
  obtain ⟨hinv, h⟩ := andB_parts h
  obtain ⟨hne, hcj⟩ := andB_parts h
  have pE : ∀ k < 27, PairOK (eP k) (getN 0 (colK R 70 0) k) (getN 0 (colK R 70 1) k) := by
    intro k hk
    rw [colK_get0 R 70 hk, colK_get1 R 70 hk]
    exact hR.2.2 (70 + k) (by omega)
  have pG : ∀ k < 27, PairOK (gP k) (getN 0 (colK R 110 0) k) (getN 0 (colK R 110 1) k) := by
    intro k hk
    rw [colK_get0 R 110 hk, colK_get1 R 110 hk]
    exact hR.2.2 (110 + k) (by omega)
  have hI := CFSG.KS.SporSch.J4B.id_enc hK
  have hI2 : encN O.one = one := hI.2
  unfold threeOK
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨List.all_eq_true.1 c12610lt, cEOK_ok⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have p := pE 0 (by omega)
    exact slpB_eq p.1.1 hI.1 (by rw [p.1.2, hI2]; exact h0)
  · intro k hk l hl
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hcl k (List.mem_range.2 hk)) l (List.mem_range.2 hl)
    rw [CFSG.KC.J4Slp.strictB_eq] at h1
    obtain ⟨m, hm, hb⟩ := List.any_eq_true.1 h1
    have hm' := List.mem_range.1 hm
    have p := mulP_ok hK (pE k hk) (pE l hl)
    exact ⟨m, hm', slpB_eq p.1.1 (pE m hm').1.1 (by rw [p.1.2, (pE m hm').1.2]; exact hb)⟩
  · intro k hk
    obtain ⟨m, hm, hb⟩ := List.any_eq_true.1 (List.all_eq_true.1 hinv k (List.mem_range.2 hk))
    have hm' := List.mem_range.1 hm
    have p := invP_ok (pE k hk)
    exact ⟨m, hm', slpB_eq p.1.1 (pE m hm').1.1 (by rw [p.1.2, (pE m hm').1.2]; exact hb)⟩
  · intro k hk l hl
    have h1 := List.all_eq_true.1 (List.all_eq_true.1 hne k (List.mem_range.2 hk)) l (List.mem_range.2 hl)
    by_cases hkl : k = l
    · subst hkl
      simp
    · have hb : Nat.beq k l = false := beq_false_of_ne hkl
      rw [hb] at h1
      have h2 : neK rm (getN 0 (colK R 70 0) k) (getN 0 (colK R 70 0) l) = true := h1
      rw [slpB_neOK (pE k hk).1.1 (pE l hl).1.1, (pE k hk).1.2, (pE l hl).1.2, h2]
      simp
  · intro k hk
    have h1 := List.all_eq_true.1 hcj k (List.mem_range.2 hk)
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · have hb : Nat.beq k 0 = false := beq_false_of_ne hk0
      rw [hb] at h1
      have h2 : Nat.beq (mulJ c rm (mulJ c rm (getN 0 (colK R 110 0) k) (getN 0 (colK R 70 0) k))
          (getN 0 (colK R 110 1) k)) CE = true := h1
      have p := mulP_ok hK (mulP_ok hK (pG k hk) (pE k hk)) (invP_ok (pG k hk))
      rw [slpB_eq p.1.1 wfN_cE (by rw [p.1.2]; exact h2)]
      simp

theorem c12610_regs : RegsOK 140 threeRegs threeR :=
  runK_ok CertificateChecks.KernelSporSch.J4Real.hK (slpB_init_ok (by norm_num)) threeProg c12610lt

theorem threeOK_ok : threeOK = true := by
  have h := c12610run
  rw [slpB_forceB_eq] at h
  exact three_of threeR c12610_regs h

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem c12610 : threeOK = true := threeOK_ok

end CertificateChecks.KernelJ4Gam

end

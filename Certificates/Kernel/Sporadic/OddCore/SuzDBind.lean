module

public import Certificates.Kernel.Sporadic.OddCore.SuzDData
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.Certificates.Kernel.PermToolSound
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import CFSG.Sporadic.SuzOddCore.CTICheckInputs
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.SuzOddCore.InvArrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34KSnd
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.SuzDK

@[expose] noncomputable def fixL0 : List Nat :=
  (List.range 1782).filter fun p => Nat.beq (pg 11 (mask 11) (SuzTP 0) p) p

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 42 6 (mask 6) p q

@[expose] noncomputable def D (j : Nat) : Nat :=
  pc (pc (pc (K 1) (K (Nat.add j 2))) (KI 1)) (KI (Nat.add j 2))

theorem kL0 : Nat.beq fixL0.length 42 = true := by quickRfl

theorem kRes : allN 22 (fun j => canonK 1782 11 (mask 11) (1782 * 11) (SuzInvT0.F (Nat.add 32 j)) &&
    Nat.beq (CFSG.KC.PermTool.restrictK 11 6 fixL0 (SuzInvT0.F (Nat.add 32 j))) (K j)) = true := by
  quickRfl

theorem kInv : allN 22 (fun j => canonK 42 6 (mask 6) (42 * 6) (K j) &&
    (canonK 42 6 (mask 6) (42 * 6) (KI j) && Nat.beq (pc (K j) (KI j)) (pidn 42 6))) = true := by
  quickRfl

theorem kNeg : (Nat.beq (pc (K 0) (KI 1)) (pidn 42 6)).not = true := by quickRfl

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases e : a = b
  · subst e
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · have h : Nat.beq a b = false := by
      cases h : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) e
    rw [h]
    exact beq_false_of_ne e

theorem fixList_eq : fixList 0 = fixL0 := by
  unfold fixList fixL0 fixedList
  rw [(CertificateChecks.KernelSpor.OddCore.rep_facts (i := 0) (by decide)).1]
  refine List.filter_congr fun p hp => ?_
  rw [CFSG.KC.BfsPin.unpack_get' (List.mem_range.1 hp), beq_nat]

theorem fixL0_length : fixL0.length = 42 := Nat.eq_of_beq_eq_true kL0

theorem kparts {j : Nat} (hj : j < 22) : canonK 42 6 (mask 6) (42 * 6) (K j) = true ∧
    canonK 42 6 (mask 6) (42 * 6) (KI j) = true ∧ pc (K j) (KI j) = pidn 42 6 := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kInv j hj
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1, h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem kGens_size : (kGens 0).size = 22 := by
  simp [kGens, invInnerGenArrs, invInnerGenCounts]

theorem kGens_get {j : Nat} (hj : j < 22) : (kGens 0)[j]! = unpack 42 6 (K j) := by
  unfold kGens
  rw [map_get _ (by simpa [invInnerGenArrs, invInnerGenCounts] using hj)]
  have e : (invInnerGenArrs 0)[j]! = invRun 0 (32 + j) := by
    rw [getElem!_pos _ j (by simpa [invInnerGenArrs, invInnerGenCounts] using hj)]
    simp only [invInnerGenArrs, Array.getElem_ofFn]
    rfl
  rw [e, SuzInv.run_eq0 (by omega), fixList_eq]
  have hL : ∀ x ∈ fixL0, x < 1782 := fun x hx => List.mem_range.1 (List.mem_filter.1 hx).1
  have hr := CFSG.KS.Raw.Orb.allN_iff.1 kRes j hj
  simp only [Bool.and_eq_true] at hr
  have e2 : Nat.add 32 j = 32 + j := rfl
  rw [e2] at hr
  rw [CFSG.KC.PermTool.restrictArr_unpack (w' := 6) hr.1 hL (by rw [fixL0_length]; decide),
    fixL0_length, Nat.eq_of_beq_eq_true hr.2]

theorem kInvs_get {j : Nat} (hj : j < 22) : (kInvs 0)[j]! = unpack 42 6 (KI j) := by
  unfold kInvs
  rw [map_get _ (by rw [kGens_size]; exact hj), kGens_get hj, fixList_eq, fixL0_length]
  obtain ⟨c1, c2, e⟩ := kparts hj
  exact invTab_eq_of_pcomp c1 c2 e

theorem D_canon {j : Nat} (hj : j < 5) : canonK 42 6 (mask 6) (42 * 6) (D j) = true := by
  obtain ⟨a1, b1, -⟩ := kparts (j := 1) (by omega)
  obtain ⟨a2, b2, -⟩ := kparts (j := j + 2) (by omega)
  unfold D pc
  exact canonK_pcomp (canonK_pcomp (canonK_pcomp a1 a2) b1) b2

theorem dGens_get {j : Nat} (hj : j < 5) : dGens[j]! = unpack 42 6 (D j) := by
  unfold dGens
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  obtain ⟨a1, b1, -⟩ := kparts (j := 1) (by omega)
  obtain ⟨a2, b2, -⟩ := kparts (j := j + 2) (by omega)
  simp only
  unfold commTab D pc
  rw [kGens_get (by omega), kGens_get (by omega), kInvs_get (by omega), kInvs_get (by omega),
    comp_unpack' a1 a2, comp_unpack' (canonK_pcomp a1 a2) b1,
    comp_unpack' (canonK_pcomp (canonK_pcomp a1 a2) b1) b2]

end CertificateChecks.KernelSpor.SuzD

end

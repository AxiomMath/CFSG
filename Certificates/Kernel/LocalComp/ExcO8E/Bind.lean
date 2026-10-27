module

public import Certificates.Kernel.LocalComp.ExcO8E.Data
public import Certificates.Kernel.LocalComp.ExcGlue
public import Certificates.Kernel.LocalComp.E8Tables
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.ExcO8E

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.ComponentClassification.RankTwoClassical.ExcO8E
open CFSG.Monster.B.Co2.Native CertificateChecks.KernelLC.ExcGlue
open CertificateChecks.KernelLC (E8.RT E8.NEG)

@[expose] noncomputable def wordNK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 240 8)
    (fun r _ ih => pcomp 240 8 (mask 8) (E8.RT r) ih) l

@[expose] noncomputable def EL : List Nat := [E0, E1, E2, E3, E4, E5, E6, E7]

theorem kId240 : idK 240 8 (mask 8) = true := by quickRfl

theorem cId240 : canonK 240 8 (mask 8) (240 * 8) (pidn 240 8) = true := by quickRfl

theorem kCR : allN 240 (fun r => canonK 240 8 (mask 8) (240 * 8) (E8.RT r)) = true := by quickRfl

theorem wordArr_unpack : ∀ (l : List Nat), (∀ r ∈ l, r < 240) →
    wordArr l = unpack 240 8 (wordNK l) ∧ canonK 240 8 (mask 8) (240 * 8) (wordNK l) = true
  | [], _ => ⟨by rw [wordArr]; exact (idK_sound kId240).symm, cId240⟩
  | r :: l, h => by
    have hr : r < 240 := h r List.mem_cons_self
    obtain ⟨ih, ihc⟩ := wordArr_unpack l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hc := allN_spec kCR r hr
    refine ⟨?_, CFSG.KC.BfsPin.canonK_pcomp hc ihc⟩
    rw [wordArr, ih, CertificateChecks.KernelLC.E8.refl_eq r hr]
    exact CFSG.KC.BfsPin.compA_unpack hc ihc

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem pairA_unpack {P Q E : Nat}
    (h1 : allN 240 (fun j => Nat.beq (pg 9 (mask 9) E j) (pg 8 (mask 8) P j)) = true)
    (h2 : allN 240 (fun j => Nat.beq (pg 9 (mask 9) E (Nat.add j 240))
      (Nat.add (pg 8 (mask 8) Q j) 240)) = true) :
    pairA (unpack 240 8 P) (unpack 240 8 Q) = unpack 480 9 E := by
  have key : ∀ j : Fin 480, (if j.val < 240 then (unpack 240 8 P)[j.val]!
      else (unpack 240 8 Q)[j.val - 240]! + 240) = pg 9 (mask 9) E j.val := by
    intro j
    by_cases hlt : j.val < 240
    · rw [ite_eq_left hlt, unpack_get hlt]
      exact (Nat.eq_of_beq_eq_true (allN_spec h1 j.val hlt)).symm
    · have hj := j.isLt
      rw [ite_eq_right hlt, unpack_get (by omega : j.val - 240 < 240)]
      have e := Nat.eq_of_beq_eq_true (allN_spec h2 (j.val - 240) (by omega))
      have hi' : Nat.add (j.val - 240) 240 = j.val := by change j.val - 240 + 240 = j.val; omega
      rw [hi'] at e
      exact e.symm
  unfold pairA unpack
  exact congrArg (Array.ofFn (n := 480)) (funext key)

theorem omWords_lt : ∀ k < 8, ∀ r ∈ omWords.getD k [], r < 240 := by decide +kernel

theorem rho_lt : ∀ i < 8, rhoPerm.getD i 0 < 8 := by decide +kernel

theorem eArrs_get (i : Nat) (hi : i < 8) : eArrs[i]! =
    pairA (wordArr (omWords.getD (rhoPerm.getD i 0) [])) (wordArr (omWords.getD i [])) := by
  rw [eArrs, getElem!_pos _ i (by simpa using hi), List.getElem_toArray, List.getElem_map,
    List.getElem_range]

theorem kE : allN 8 (fun i => bAnd(
    strictB (wordNK (omWords.getD (rhoPerm.getD i 0) [])) (fun W =>
      allN 240 (fun j => Nat.beq (pg 9 (mask 9) (lget EL i) j) (pg 8 (mask 8) W j))),
    strictB (wordNK (omWords.getD i [])) (fun W =>
      allN 240 (fun j => Nat.beq (pg 9 (mask 9) (lget EL i) (Nat.add j 240))
        (Nat.add (pg 8 (mask 8) W j) 240))))) = true := by quickRfl

theorem eArrs_eq (i : Nat) (hi : i < 8) : eArrs[i]! = unpack 480 9 (lget EL i) := by
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec kE i hi)
  rw [CFSG.KS.PF.strictB_eqP] at h1 h2
  rw [eArrs_get i hi, (wordArr_unpack _ (omWords_lt _ (rho_lt i hi))).1,
    (wordArr_unpack _ (omWords_lt i hi)).1]
  exact pairA_unpack h1 h2

theorem kZ1a : allN 240 (fun j => Nat.beq (pg 9 (mask 9) Z1 j) (pg 8 (mask 8) E8.NEG j)) = true :=
  by quickRfl
theorem kZ1b : allN 240 (fun j => Nat.beq (pg 9 (mask 9) Z1 (Nat.add j 240))
    (Nat.add (pg 8 (mask 8) (pidn 240 8) j) 240)) = true := by quickRfl
theorem kZ2a : allN 240 (fun j => Nat.beq (pg 9 (mask 9) Z2 j) (pg 8 (mask 8) (pidn 240 8) j)) =
    true := by quickRfl
theorem kZ2b : allN 240 (fun j => Nat.beq (pg 9 (mask 9) Z2 (Nat.add j 240))
    (Nat.add (pg 8 (mask 8) E8.NEG j) 240)) = true := by quickRfl
theorem kZ3a : allN 240 (fun j => Nat.beq (pg 9 (mask 9) Z3 j) (pg 8 (mask 8) E8.NEG j)) = true :=
  by quickRfl
theorem kZ3b : allN 240 (fun j => Nat.beq (pg 9 (mask 9) Z3 (Nat.add j 240))
    (Nat.add (pg 8 (mask 8) E8.NEG j) 240)) = true := by quickRfl

theorem z1_eq : pairA negArr (idA 240) = unpack 480 9 Z1 := by
  rw [CertificateChecks.KernelLC.E8.neg_eq, ← idK_sound kId240]
  exact pairA_unpack kZ1a kZ1b

theorem z2_eq : pairA (idA 240) negArr = unpack 480 9 Z2 := by
  rw [CertificateChecks.KernelLC.E8.neg_eq, ← idK_sound kId240]
  exact pairA_unpack kZ2a kZ2b

theorem z3_eq : pairA negArr negArr = unpack 480 9 Z3 := by
  rw [CertificateChecks.KernelLC.E8.neg_eq]
  exact pairA_unpack kZ3a kZ3b

end CertificateChecks.KernelLC.ExcO8E

end

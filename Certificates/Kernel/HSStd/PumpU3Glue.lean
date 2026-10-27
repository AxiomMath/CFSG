module

public import Certificates.Kernel.HSStd.PumpU3Checks
public import Certificates.Kernel.LocalComp.L39Binds
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.BfsPinSetSound
public import CFSG.Certificates.Kernel.LocalCompExcDerivSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHSStd.PumpU3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CertificateChecks.KernelLC.L39
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.EvenSporadicStandard.HSStd.FiveY CFSG.EvenSporadicStandard.HSStd.PumpTC7
open CFSG.EvenSmallLie.Child3.SelL39
open CFSG.KC.LocalComp.ExcDeriv (fixCntK fixCntK_eq)

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

theorem nums' : U.ng = 6 ∧ U.N = 729 := by
  have h := nums
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem enumOKL_of_enumOK {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (h : enumOK n gs ps c = true) : enumOKL n gs ps c = true := by
  simp only [enumOK, enumOKL, arrCertOK, arrCertOKL, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, List.isChain_iff_pairwise.2 h.2.2.2.2⟩

theorem fixCount_unpack (P : ℕ) : fixCount (unpack 182 8 P) = fixCntK 8 (mask 8) P 182 := by
  rw [fixCntK_eq]
  have e : ((Finset.range 182).filter fun p => (unpack 182 8 P)[p]! = p).card =
      (List.range 182).countP (fun p => decide ((unpack 182 8 P)[p]! = p)) := by
    rw [List.countP_eq_length_filter]
    rfl
  rw [fixCount, e]
  refine List.countP_congr fun p hp => ?_
  rw [unpack_get' (List.mem_range.1 hp)]
  cases h : Nat.beq (pg 8 (mask 8) P p) p
  · have hne : pg 8 (mask 8) P p ≠ p := fun h' => by
      rw [h', Nat.beq_refl] at h
      exact Bool.false_ne_true h.symm
    simp [hne]
  · simp [Nat.eq_of_beq_eq_true h]

theorem tS_binds : tS.size = 7 ∧ ∀ j < 7, tS[j]! = unpack 182 8 (LT.S j) :=
  ⟨bindsLT.2.2.2.1, bindsLT.2.2.2.2.1⟩

theorem u_get : ∀ k < U.ng, uGens[k]! = unpack 182 8 (U.G k) := by
  intro k hk
  rw [nums'.1] at hk
  have h := wordEqK_sound tS_binds permLT (allN_spec gU k hk)
  have hl : k < uWords.length := by
    have : uWords.length = 6 := rfl
    omega
  have e : uGens[k]! = tW (uWords.getD k []) := by
    simp [uGens, getElem!_def, hl, List.getD_eq_getElem?_getD]
  rw [e, tW]
  exact h.1

theorem hsz : uGens.size = U.ng := by
  rw [nums'.1]
  simp [uGens, uWords]

theorem hps : ∀ p ∈ tKeys, p < 182 := by decide

theorem hp : ∀ k < U.ng, permOK 182 8 (mask 8) (182 * 8) (U.G k) (pinvS 182 8 (mask 8) (U.G k)) =
    true := fun k hk => allN_spec gPerm k (nums'.1 ▸ hk)

theorem uPts : uCert.pts = Array.ofFn (n := U.N) fun i => unpack 182 8 (U.T i.val) :=
  enumBfs_pts_base hsz u_get U.ok hps kU (by rw [nums'.2]; omega)

theorem uOK : enumOK 182 uGens tKeys uCert = true :=
  enumOK_of_bfsK_base hsz u_get hp U.ok hps kU (by rw [nums'.2]; omega)

theorem g7_eq : g7 = unpack 182 8 g7P := (wordEqK_sound tS_binds permLT g7w).1

theorem u3OK_true : u3OK = true := by
  obtain ⟨hab, hfix7⟩ := and_of g7ok
  obtain ⟨hperm7, hpow⟩ := and_of hab
  have hpp7 : PP 182 8 g7P := PP_of_permOK sz hperm7
  have h1 : enumOKL 182 uGens tKeys uCert = true := enumOKL_of_enumOK uOK
  have h2 : (uCert.pts.size == 729) = true := by
    rw [uPts, Array.size_ofFn, nums'.2]
    rfl
  have h3 : uCert.pts.toList.all (fun a => eqA 182 a (idA 182) || fixCount a == 2 ||
      fixCount a == 20) = true := by
    rw [uPts, Array.toList_ofFn, List.all_eq_true]
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    have hpi : PP 182 8 (U.T i) := PP_pts U.ok hp i i.2
    rw [idA_eq sz, eqA_PP hpi (PP.id sz), fixCount_unpack]
    have := allN_spec fixU i i.2
    simp only [Bool.or_eq_true, beq_iff_eq, Nat.beq_eq] at this ⊢
    exact this
  have h4 : validA 182 g7 = true := by
    rw [g7_eq]
    exact validA_unpack hperm7
  have a1 := hpp7.mul hpp7
  have a2 := hpp7.mul a1
  have a3 := hpp7.mul a2
  have a4 := hpp7.mul a3
  have a5 := hpp7.mul a4
  have a6 := hpp7.mul a5
  have h5 : eqA 182 (compA 182 g7 (compA 182 g7 (compA 182 g7 (compA 182 g7
      (compA 182 g7 (compA 182 g7 g7)))))) (idA 182) = true := by
    rw [g7_eq, compA_PP hpp7 hpp7, compA_PP hpp7 a1, compA_PP hpp7 a2, compA_PP hpp7 a3,
      compA_PP hpp7 a4, compA_PP hpp7 a5, idA_eq sz, eqA_PP a6 (PP.id sz)]
    exact hpow
  have h6 : (fixCount g7 == 0) = true := by
    rw [g7_eq, fixCount_unpack]
    simp only [beq_iff_eq, Nat.beq_eq] at hfix7 ⊢
    exact hfix7
  rw [u3OK]
  simp only [h1, h2, h3, h4, h5, h6, Bool.and_self]

end CertificateChecks.KernelHSStd.PumpU3

end

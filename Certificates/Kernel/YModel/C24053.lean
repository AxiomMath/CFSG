module

public import Certificates.Kernel.YModel.Y432F
public import Certificates.Kernel.Fi24PG10.Rels
public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierModelInputs
public import CFSG.Certificates.Kernel.YModel.C24053.Data
public import CFSG.Monster.GMS.R433Cover.Algebra
import CFSG.Certificates.Kernel.YModel.C24053.CheckA
import CFSG.Certificates.Kernel.YModel.C24053.CheckB

public section

namespace CertificateChecks.KernelYModel

open CFSG.KC.YModel CFSG.YGroups CFSG.KD.C24053 CertificateChecks.KernelPG10 CFSG.CosetTable
  CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_append evalWord_nil evalWord_cons)

set_option maxRecDepth 100000

theorem c24053_chk : ∀ j < 136, x1Chk24053_ j = true := by
  intro j hj
  interval_cases j
  exacts [x1Chk24053_0, x1Chk24053_1, x1Chk24053_2, x1Chk24053_3, x1Chk24053_4, x1Chk24053_5,
    x1Chk24053_6, x1Chk24053_7, x1Chk24053_8, x1Chk24053_9, x1Chk24053_10, x1Chk24053_11,
    x1Chk24053_12, x1Chk24053_13, x1Chk24053_14, x1Chk24053_15, x1Chk24053_16, x1Chk24053_17,
    x1Chk24053_18, x1Chk24053_19, x1Chk24053_20, x1Chk24053_21, x1Chk24053_22, x1Chk24053_23,
    x1Chk24053_24, x1Chk24053_25, x1Chk24053_26, x1Chk24053_27, x1Chk24053_28, x1Chk24053_29,
    x1Chk24053_30, x1Chk24053_31, x1Chk24053_32, x1Chk24053_33, x1Chk24053_34, x1Chk24053_35,
    x1Chk24053_36, x1Chk24053_37, x1Chk24053_38, x1Chk24053_39, x1Chk24053_40, x1Chk24053_41,
    x1Chk24053_42, x1Chk24053_43, x1Chk24053_44, x1Chk24053_45, x1Chk24053_46, x1Chk24053_47,
    x1Chk24053_48, x1Chk24053_49, x1Chk24053_50, x1Chk24053_51, x1Chk24053_52, x1Chk24053_53,
    x1Chk24053_54, x1Chk24053_55, x1Chk24053_56, x1Chk24053_57, x1Chk24053_58, x1Chk24053_59,
    x1Chk24053_60, x1Chk24053_61, x1Chk24053_62, x1Chk24053_63, x1Chk24053_64, x1Chk24053_65,
    x1Chk24053_66, x1Chk24053_67, x1Chk24053_68, x1Chk24053_69, x1Chk24053_70, x1Chk24053_71,
    x1Chk24053_72, x1Chk24053_73, x1Chk24053_74, x1Chk24053_75, x1Chk24053_76, x1Chk24053_77,
    x1Chk24053_78, x1Chk24053_79, x1Chk24053_80, x1Chk24053_81, x1Chk24053_82, x1Chk24053_83,
    x1Chk24053_84, x1Chk24053_85, x1Chk24053_86, x1Chk24053_87, x1Chk24053_88, x1Chk24053_89,
    x1Chk24053_90, x1Chk24053_91, x1Chk24053_92, x1Chk24053_93, x1Chk24053_94, x1Chk24053_95,
    x1Chk24053_96, x1Chk24053_97, x1Chk24053_98, x1Chk24053_99, x1Chk24053_100, x1Chk24053_101,
    x1Chk24053_102, x1Chk24053_103, x1Chk24053_104, x1Chk24053_105, x1Chk24053_106,
    x1Chk24053_107, x1Chk24053_108, x1Chk24053_109, x1Chk24053_110, x1Chk24053_111,
    x1Chk24053_112, x1Chk24053_113, x1Chk24053_114, x1Chk24053_115, x1Chk24053_116,
    x1Chk24053_117, x1Chk24053_118, x1Chk24053_119, x1Chk24053_120, x1Chk24053_121,
    x1Chk24053_122, x1Chk24053_123, x1Chk24053_124, x1Chk24053_125, x1Chk24053_126,
    x1Chk24053_127, x1Chk24053_128, x1Chk24053_129, x1Chk24053_130, x1Chk24053_131,
    x1Chk24053_132, x1Chk24053_133, x1Chk24053_134, x1Chk24053_135]

theorem c24053_inv (c : ℕ) : arrGen 31671 y432FArrays c * arrGen 31671 y432FArrays c = 1 := by
  by_cases hc : c < 10
  · have hm : [c, c] ∈ yRels 4 3 2 := by interval_cases c <;> decide +kernel
    have h := evalWord_arrGen_eq_one y432F_perms y432F_relators [c, c] hm
    rwa [evalWord_cons, evalWord_cons, evalWord_nil, mul_one] at h
  · rw [arrGen_of_le (by rw [y432F_size]; omega), one_mul]

theorem c24053_val {u : List ℕ} (h : weqK 15 10 CFSG.KD.YMY432F.Nf u [] = true) :
    evalWord (arrGen 31671 y432FArrays) u = 1 := by
  have h2 : CFSG.Monster.B.Co2.Native.eqA 31671 (ModelNative.evalW 31671 y432FArrays u)
      (ModelNative.evalW 31671 y432FArrays []) = true := by
    rw [y432F_arrays_eq, eqA_of_weqK _ _ y432F_let]
    exact h
  have h3 := (evalWord_arrGen_eq_iff y432F_perms u []).2 h2
  rwa [evalWord_nil] at h3

theorem c24053_expL_inv (l : ℕ × Bool) : expL (l.1, !l.2) = (expL l).reverse := by
  obtain ⟨x, s⟩ := l
  cases s <;> simp [expL]

theorem c24053_flat_invW (w : List (ℕ × Bool)) :
    (CFSG.KD.C24053.invW w).flatMap expL = (w.flatMap expL).reverse := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    have e : CFSG.KD.C24053.invW (l :: w) = CFSG.KD.C24053.invW w ++ [(l.1, !l.2)] := by
      simp [CFSG.KD.C24053.invW]
    rw [e, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      c24053_expL_inv, List.flatMap_cons, List.reverse_append]

theorem c24053_rev {u : List ℕ} (h : evalWord (arrGen 31671 y432FArrays) u = 1) :
    evalWord (arrGen 31671 y432FArrays) u.reverse = 1 := by
  rw [CFSG.Monster.GMS.R433Cover.evalWord_reverse_inv c24053_inv, h, inv_one]

theorem c24053_rot {u v : List ℕ} (h : evalWord (arrGen 31671 y432FArrays) (u ++ v) = 1) :
    evalWord (arrGen 31671 y432FArrays) (v ++ u) = 1 := by
  rw [evalWord_append] at h ⊢
  exact mul_eq_one_comm.mp h

theorem c24053_rel (j : ℕ) (hj : j < 136) (hk : keep j = true) :
    evalWord (arrGen 31671 y432FArrays) (rel j) = 1 := by
  have h := c24053_chk j hj
  rw [x1Chk24053_, hk] at h
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h
  rcases h with hp | hw
  · simp only [pairOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨hodd, hk1⟩, he⟩ := hp
    have h1 := c24053_chk (j - 1) (by omega)
    have hev : (j - 1) % 2 = 0 := by omega
    have hp1 : pairOK (j - 1) = false := by simp [pairOK, hev]
    rw [x1Chk24053_, hk1, hp1] at h1
    have hv := c24053_val (by simpa using h1)
    rcases he with e | e
    · rw [rel, e, c24053_flat_invW]
      exact c24053_rev hv
    · rw [rel, e, rot1, List.flatMap_append]
      apply c24053_rot
      rw [← List.flatMap_append, List.take_append_drop, c24053_flat_invW]
      exact c24053_rev hv
  · exact c24053_val hw

theorem c24053_map {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) :
    (restrictWords (subsetOf m KernelPG10.S0) ws).map expandX = ((List.range 136).filter keep).map rel := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem c24053_r0_of {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) :
    ((ws.getD 106 []).filter fun l => l.1.val == 8).length % 2 = 1 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem c24053_r0 : ((X0.getD r0Idx []).filter fun l => l.1.val == 8).length % 2 = 1 :=
  c24053_r0_of m0_eq x0_letters

theorem c24053_rels : ∀ w ∈ X1, evalWord (arrGen 31671 y432FArrays) (expandX w) = 1 := by
  intro w hw
  have hm : expandX w ∈ ((List.range 136).filter keep).map rel := by
    rw [← c24053_map m0_eq x0_letters]
    exact List.mem_map_of_mem hw
  obtain ⟨j, hj, e⟩ := List.mem_map.mp hm
  rw [List.mem_filter, List.mem_range] at hj
  rw [← e]
  exact c24053_rel j hj.1 hj.2

end CertificateChecks.KernelYModel

end

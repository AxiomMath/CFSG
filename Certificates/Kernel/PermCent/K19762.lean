module

public import Certificates.Data.Kernel.PermCent.M11PairQ
import CFSG.Certificates.Kernel.PermCent.CVSound
import CFSG.GH74.KGroups.PermCheck
import CFSG.Sporadic.Schreier.M11Check

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelPermCent

open CFSG.Certificates CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkCV.M11B
  CFSG.Sporadic.Schreier CFSG.GH74.KGroups

theorem k19762_word : wordC = true := by decide +kernel

theorem k19762_conj : m11ConjOK = true := by decide +kernel

theorem k19762_inv : (E.filter (orderIsP · 2 [2])).length = 165 := by decide +kernel

theorem k19762_fix : m11FixCnt = 48 := by decide +kernel

theorem orderIsP_conj19762 {G : Type*} [Group G] [DecidableEq G] (g x : G) (m : Nat)
    (ps : List Nat) : orderIsP (g * x * g⁻¹) m ps = orderIsP x m ps := by
  simp only [orderIsP, conj_pow, conj_eq_one_iff]

theorem count_prod_conj19762 {G : Type*} [Group G] [DecidableEq G] (I F T : List G) (x0 : G)
    (P : G → G → Bool) (hF : F.Nodup) (hFc : ∀ g ∈ T, ∀ y, g * y * g⁻¹ ∈ F ↔ y ∈ F)
    (hP : ∀ g x y, P (g * x * g⁻¹) (g * y * g⁻¹) = P x y)
    (hI : ∀ x ∈ I, ∃ g ∈ T, g * x0 * g⁻¹ = x) :
    ((I ×ˢ F).filter fun q => P q.1 q.2).length = I.length * (F.filter (P x0)).length := by
  have hterm : ∀ x ∈ I, F.countP (P x) = F.countP (P x0) := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hI x hx
    have hinj : Function.Injective fun y : G => g * y * g⁻¹ := fun a b h => by simpa using h
    have hperm : (F.map fun y => g * y * g⁻¹).Perm F := by
      refine (List.perm_ext_iff_of_nodup (hF.map hinj) hF).2 fun y => ?_
      rw [List.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (hFc g hg z).2 hz
      · intro hy
        have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
        refine ⟨g⁻¹ * y * g, (hFc g hg _).1 ?_, e⟩
        rw [e]
        exact hy
    rw [← hperm.countP_eq, List.countP_map]
    simp only [Function.comp_def, hP]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  simp only [SProd.sprod, List.product, List.countP_flatMap, List.countP_map, Function.comp_def]
  rw [List.map_congr_left hterm, List.map_const', List.sum_replicate, smul_eq_mul]

theorem k19762_count : pairCntC = 7920 := by
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  have hE : elemsT m11Certificate = E.map ev := elemsT_eq_elemsC m11Certificate
  have hmemE : ∀ a : CV 11, a ∈ E ↔ ev a ∈ m11Certificate.originalSubgroup := fun a => by
    rw [← mem_elemsT _ hQ, hE, mem_map_ev]
  have hnd : E.Nodup := List.Nodup.of_map ev (hE ▸ nodup_elemsT _ hQ)
  have hFc : ∀ g ∈ m11ConjT, ∀ y, g * y * g⁻¹ ∈ E.filter (orderIsP · 4 [2]) ↔
      y ∈ E.filter (orderIsP · 4 [2]) := by
    intro g hg y
    have hg' := (hmemE g).1 (mem_pickGaps hg)
    simp only [List.mem_filter, orderIsP_conj19762]
    rw [hmemE, hmemE, ev_mul, ev_mul, ev_inv,
      Subgroup.mul_mem_cancel_right _ (inv_mem hg'), Subgroup.mul_mem_cancel_left _ hg']
  have hP : ∀ g x y : CV 11,
      (orderIsP (g * x * g⁻¹ * (g * y * g⁻¹)) 11 [11] &&
        orderIsP (g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹) 6 [2, 3] &&
        orderIsP (g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * x * g⁻¹) *
          (g * y * g⁻¹) * (g * y * g⁻¹)) 5 [5]) =
      (orderIsP (x * y) 11 [11] && orderIsP (x * y * x⁻¹ * y⁻¹) 6 [2, 3] &&
        orderIsP (x * y * x * y⁻¹ * x * y * y) 5 [5]) := by
    intro g x y
    have e1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    have e2 : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ * (g * y * g⁻¹)⁻¹ =
        g * (x * y * x⁻¹ * y⁻¹) * g⁻¹ := by group
    have e3 : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ * (g * x * g⁻¹) *
        (g * y * g⁻¹) * (g * y * g⁻¹) = g * (x * y * x * y⁻¹ * x * y * y) * g⁻¹ := by group
    rw [e3, e2, e1, orderIsP_conj19762, orderIsP_conj19762, orderIsP_conj19762]
  have hI : ∀ x ∈ E.filter (orderIsP · 2 [2]), ∃ g ∈ m11ConjT, g * m11X0 * g⁻¹ = x := by
    intro x hx
    have h := List.all_eq_true.1 k19762_conj x hx
    rw [decide_eq_true_iff, m11ConjJ, List.mem_map] at h
    exact h
  have hfix : ((E.filter (orderIsP · 4 [2])).filter fun y =>
      orderIsP (m11X0 * y) 11 [11] && orderIsP (m11X0 * y * m11X0⁻¹ * y⁻¹) 6 [2, 3] &&
        orderIsP (m11X0 * y * m11X0 * y⁻¹ * m11X0 * y * y) 5 [5]).length = 48 := by
    rw [← k19762_fix, m11FixCnt]
    exact congrArg List.length (List.filter_congr fun y _ => (pairPQ_eq m11X0 y).symm)
  rw [pairCntC]
  refine (count_prod_conj19762 (E.filter (orderIsP · 2 [2])) (E.filter (orderIsP · 4 [2])) m11ConjT
    m11X0 (fun x y => orderIsP (x * y) 11 [11] && orderIsP (x * y * x⁻¹ * y⁻¹) 6 [2, 3] &&
      orderIsP (x * y * x * y⁻¹ * x * y * y) 5 [5]) (hnd.filter _) hFc hP hI).trans ?_
  rw [k19762_inv, hfix]

end CertificateChecks.KernelPermCent

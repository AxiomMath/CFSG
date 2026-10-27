module

public import Certificates.Kernel.SmithL6K.ChecksU
public import Certificates.Kernel.SmithL6K.ChecksU0
public import Certificates.Kernel.SmithL6K.ChecksU1
public import Certificates.Kernel.SmithL6K.ChecksU2
public import Certificates.Kernel.SmithL6K.ChecksU3
public import Certificates.Kernel.SmithL6K.ChecksU4
public import Certificates.Kernel.SmithL6K.ChecksU5
public import Certificates.Kernel.SmithL6K.ChecksU6
public import Certificates.Kernel.SmithL6K.GlueF
public import Certificates.Kernel.SmithL6K.GlueA
public import CFSG.Certificates.Kernel.SmithL6KUSound
public import CFSG.Certificates.Kernel.SmithL6KRSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel CFSG.SmithL6.CollK
open CFSG.SmithE (applyCols)

theorem tvc_code : ∀ k < 1953, tvc.getD k 0 = codeOf (tvPair k) := fun _ hk =>
  (tvPair_code hk).symm

theorem p0_facts {p : Nat} (hp : p ∈ p0) : p < 1953 ∧ inPlane 0 p = true :=
  mem_planePts0 p0_planePts hp

theorem p0_len : p0.length = 49 := by decide +kernel

theorem planePts0_eq : planePtsArr[0]! = p0.toArray := by
  rw [planePtsArr_get (by decide), p0_planePts]

theorem ua_rows_all : ∀ i < 7, uaRowsC (ugC tvc) tvc (((uaRC tvc p0).drop (7 * i)).take 7) = true
  | 0, _ => ua_rows0_ok
  | 1, _ => ua_rows1_ok
  | 2, _ => ua_rows2_ok
  | 3, _ => ua_rows3_ok
  | 4, _ => ua_rows4_ok
  | 5, _ => ua_rows5_ok
  | 6, _ => ua_rows6_ok
  | _ + 7, h => absurd h (by omega)

theorem chkUa_gens : (ugens.all fun g => decide (g < 1953) && inPlane 0 g) = true := by
  have h := ua_gens_ok
  unfold ugens at h ⊢
  rw [List.toList_toArray] at h
  rw [List.all_toArray]
  refine List.all_eq_true.mpr fun g hg => ?_
  have e := List.all_eq_true.mp h g hg
  rw [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at e
  rw [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨e.1, (p0_facts e.2).2⟩

theorem chkUa_fix : (planePtsArr[0]!.all fun p => planePtsArr[0]!.all fun q => tvTab[p]![q]! == q)
    = true := by
  rw [planePts0_eq, List.all_toArray]
  refine List.all_eq_true.mpr fun p hp => ?_
  rw [List.all_toArray]
  refine List.all_eq_true.mpr fun q hq => ?_
  have hp' := (p0_facts hp).1
  rw [tvTab_get hp' (p0_facts hq).1, uaFixC_sound tvc_code ua_fix_ok (fun p hp => (p0_facts hp).1)
    hp hq]
  exact beq_self_eq_true _

theorem chkUa_rows : ((List.range 49).all fun k => (List.range 1953).all fun x =>
    uaWord uco[k]! x == tvTab[planePtsArr[0]![k]!]![x]!) = true := by
  rw [planePts0_eq]
  refine List.all_eq_true.mpr fun k hk => List.all_eq_true.mpr fun x hx => ?_
  have hk' := List.mem_range.mp hk
  have hx' := List.mem_range.mp hx
  have hpk : p0.getD k 0 ∈ p0 := by
    rw [getD_of_lt (by rw [p0_len]; exact hk')]
    exact List.getElem_mem _
  have hp := (p0_facts hpk).1
  have hm := List.contains_iff_mem.mp (ua_slices_ok k hk')
  rw [tvc_code _ hp] at hm
  rw [toArray_get p0 k, tvTab_get hp hx',
    uaRowsC_sound tvc_length tvc_code (ua_rows_all _ (by omega)) hm hp hx']
  exact beq_self_eq_true _

theorem chkUa_move : ((List.range 512).all fun a => a == 0 || (List.range 1953).any fun x =>
    uaWord a x != x) = true := by
  refine List.all_eq_true.mpr fun a ha => ?_
  rw [Bool.or_eq_true, beq_iff_eq]
  rcases uaMoveC_sound tvc_length tvc_code ua_move_ok (List.mem_range.mp ha) with h | ⟨x, hx, h⟩
  · exact Or.inl h
  · exact Or.inr (List.any_eq_true.mpr ⟨x, List.mem_range.mpr hx, bne_iff_ne.mpr h⟩)

theorem chkUa_comm : ((List.range 1953).all fun q =>
    !(planePtsArr[0]!.all fun p => tvTab[p]![q]! == q) || inPlane 0 q) = true := by
  rw [planePts0_eq]
  refine List.all_eq_true.mpr fun q hq => ?_
  have hq' := List.mem_range.mp hq
  rw [List.all_toArray, Bool.or_eq_true]
  cases e : p0.all fun p => tvTab[p]![q]! == q
  · exact Or.inl rfl
  · refine Or.inr (p0_facts (uaCommC_sound tvc_length tvc_code ua_comm_ok
      (fun p hp => (p0_facts hp).1) hq' fun p hp => ?_)).2
    have h := beq_iff_eq.mp (List.all_eq_true.mp e p hp)
    rwa [tvTab_get (p0_facts hp).1 hq'] at h

theorem chkUa_planes : ((List.range 1395).all fun j => j == 0 ||
    planePtsArr[0]!.any fun p => planeImg p j != j) = true := by
  rw [planePts0_eq]
  refine List.all_eq_true.mpr fun j hj => ?_
  have hj' := List.mem_range.mp hj
  have h := List.all_eq_true.mp ua_planes_ok j hj
  rw [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  rw [List.any_map] at h
  obtain ⟨p, hp, h⟩ := List.any_eq_true.mp h
  refine Or.inr ?_
  rw [List.any_toArray]
  refine List.any_eq_true.mpr ⟨p, hp, ?_⟩
  have hp' := (p0_facts hp).1
  rw [bne_iff_ne]
  intro e
  obtain ⟨j', hj'', hw, -⟩ := clo_all p hp' j hj'
  have e' := planeImg_wt hp' hj' hj'' hw
  rw [e] at e'
  subst e'
  simp only [Function.comp_apply] at h
  rw [apK_tcl hp', wtd_get hj', ← hw, bne_self_eq_false] at h
  exact absurd h (by decide)

theorem chkUa_holds : chkUa = true := by
  unfold chkUa
  dsimp only
  rw [chkUa_gens, ua_uco_ok, chkUa_fix, chkUa_rows, chkUa_move, chkUa_comm, chkUa_planes]
  rfl

end CertificateChecks.KernelSmithL6K

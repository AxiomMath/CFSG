module

public import Certificates.Kernel.OmegaEight.Quat125K
public import Certificates.Kernel.OmegaEight.Quat125KC
public import Certificates.Kernel.OmegaEight.E4O8CentGlue
public import CFSG.Certificates.Kernel.O8QuatSound
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckB

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.KC.PCent CertificateChecks.KernelO8 CertificateChecks.KernelO8.E4C
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4 CFSG.Monster.B.Co2.Native
  CFSG.ClassicalInvolution.Q3.TL4.E4O8 CFSG.Monster.B.Co2

@[expose] noncomputable def q125K0 : Subgroup (Equiv.Perm (Fin 360)) :=
  Subgroup.closure {toPerm 360 9 e4U, toPerm 360 9 om0V}

theorem q125K0_eq : q125K0 = Subgroup.closure {permOfArr 360 (u0A ()), permOfArr 360 (v0A ())} := by
  rw [q125K0, e4c_u0, e4c_v0]

theorem q125_toPerm_cj {c x : Nat} (hc : CFSG.KC.BfsPin.PP 360 9 c)
    (hx : CFSG.KC.BfsPin.PP 360 9 x) :
    toPerm 360 9 (cj c x) = toPerm 360 9 c * toPerm 360 9 x * (toPerm 360 9 c)⁻¹ := by
  change toPerm 360 9 (pcomp 360 9 (mask 9) (pcomp 360 9 (mask 9) c x) (pinvS 360 9 (mask 9) c)) = _
  rw [toPerm_mul (hc.mul hx) hc.inv, toPerm_mul hc hx, toPerm_inv hc]

theorem q125_PP_cj {c x : Nat} (hc : CFSG.KC.BfsPin.PP 360 9 c)
    (hx : CFSG.KC.BfsPin.PP 360 9 x) : CFSG.KC.BfsPin.PP 360 9 (cj c x) :=
  (hc.mul hx).mul hc.inv

theorem q125_mem_K0 {x : Nat} (h : e4Mem e4L x = true) : toPerm 360 9 x ∈ q125K0 := by
  obtain ⟨-, -, -, -, -, hpx, hpu, hpv⟩ := e4c_pm
  have hU : toPerm 360 9 e4U ∈ q125K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hV : toPerm 360 9 om0V ∈ q125K0 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hX : toPerm 360 9 (mainK 0) ∈ q125K0 := by
    rw [← e4c_u0_sq]
    exact q125K0.mul_mem hU hU
  unfold e4Mem at h
  obtain ⟨l, hl, he⟩ := List.any_eq_true.1 h
  rw [Nat.eq_of_beq_eq_true he]
  simp only [e4L, e4Q, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [e4c_pid]
    exact q125K0.one_mem
  · exact hX
  · exact hU
  · rw [e4c_mul hpu hpx]
    exact q125K0.mul_mem hU hX
  · exact hV
  · rw [e4c_mul hpv hpx]
    exact q125K0.mul_mem hV hX
  · rw [e4c_mul hpu hpv]
    exact q125K0.mul_mem hU hV
  · rw [e4c_mul (p := pc e4U om0V) (hpu.mul hpv) hpx, e4c_mul hpu hpv]
    exact q125K0.mul_mem (q125K0.mul_mem hU hV) hX

theorem q125_norm {h : Nat} (hp : CFSG.KC.BfsPin.PP 360 9 h)
    (hn : e4Norms e4L e4U om0V h = true) :
    toPerm 360 9 h ∈ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360))) := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  unfold e4Norms at hn
  rw [Bool.and_eq_true] at hn
  have h1 := q125_mem_K0 hn.1
  have h2 := q125_mem_K0 hn.2
  rw [q125_toPerm_cj hp hpu] at h1
  rw [q125_toPerm_cj hp hpv] at h2
  exact CFSG.KC.O8Quat.mem_normalizer_closure_pair h1 h2

theorem q125_orderOf_v0 : orderOf (toPerm 360 9 om0V) = 4 := by
  obtain ⟨-, -, -, -, -, -, -, hpv⟩ := e4c_pm
  obtain ⟨-, hx2, hx1⟩ := e4c_x0_facts
  have hsq : toPerm 360 9 om0V ^ 2 = toPerm 360 9 (mainK 0) := by
    rw [sq, ← e4c_mul hpv hpv, Nat.eq_of_beq_eq_true kV0Sq125]
  refine CFSG.ClassicalInvolution.Q3.TL4.E4C.orderOf_eq_four (by rw [hsq]; exact hx1) ?_
  rw [show (4 : Nat) = 2 * 2 from rfl, pow_mul, hsq, sq, hx2]

theorem q125_connected {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT) :
    Relation.ReflTransGen (Vtx.StarRel omegaT q125K0) q125K0 (conjSub g q125K0) := by
  refine CFSG.KC.O8Quat.reflTransGen_of_closure e4c_omegaT (fun s hs => ?_) hg
  obtain ⟨r, hr, rfl⟩ := hs
  have hpr : CFSG.KC.BfsPin.PP 360 9 (AP.S r) := e4c_pp (root_facts hr).2.2.1
  have hmem : toPerm 360 9 (AP.S r) ∈ omegaT :=
    e4c_omegaT ▸ Subgroup.subset_closure ⟨r, hr, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hpv⟩ := e4c_pm
  have hc := allN_spec kConn125 r hr
  refine CFSG.KC.O8Quat.reflTransGen_of_norm hmem ?_
  cases hb : Nat.beq r 2
  · rw [hb] at hc
    refine Or.inr ⟨toPerm 360 9 om0V, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl),
      q125_orderOf_v0, ?_⟩
    rw [← q125_toPerm_cj hpr hpv]
    exact q125_norm (q125_PP_cj hpr hpv) hc
  · rw [hb] at hc
    obtain rfl := Nat.eq_of_beq_eq_true hb
    exact Or.inl (q125_norm hpr hc)

end CertificateChecks.KernelO8.Q125

end

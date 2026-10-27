module

public import Certificates.Kernel.J4Q.X0OrbOk
public import Certificates.Kernel.J4Q.ListAux
public import Certificates.Kernel.J4Q.LocVec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem rootV_wf' : rootV.wf = true := by decide

@[expose] noncomputable def xPV : List Nat := (List.range 6720).map fun k => getN 0 XPTS (ch64 XQL k)

theorem pts_map : x0Pts.map v2N = xPV := by
  obtain ⟨-, hmap, hwf⟩ := x0Orb_ok
  unfold x0Pts xPV
  rw [List.map_map]
  have h1 : ∀ X ∈ x0Orb.mats.toList, (v2N ∘ fun M => frApply (frTable M) rootV) X =
      (fun m => vecJ rm (v2N rootV) m) (encR X) := by
    intro X hX
    exact v2N_frApply hK (hwf X hX) rootV_wf'
  have h2 : x0Orb.mats.toList.map (fun a => (fun m => vecJ rm (v2N rootV) m) (encR a)) =
      (x0Orb.mats.toList.map encR).map (fun m => vecJ rm (v2N rootV) m) := by
    rw [List.map_map]
    rfl
  rw [List.map_congr_left h1, h2, hmap, List.map_map]
  apply List.map_congr_left
  intro k hk
  have h := xDer_spec (List.mem_range.1 hk)
  unfold xDerK at h
  simp only [andB_eq, Bool.and_eq_true] at h
  exact Nat.eq_of_beq_eq_true h.1.2

theorem pts_wf : ∀ p ∈ x0Pts, p.wf = true := by
  obtain ⟨-, -, hwf⟩ := x0Orb_ok
  intro p hp
  unfold x0Pts at hp
  obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hp
  exact wf_frApply (hwf M hM) _

theorem v2N_inj {a b : V2} (h : v2N a = v2N b) : a = b := by
  have hb := beq_v2N a b
  rw [h, Nat.beq_refl] at hb
  cases a
  cases b
  simp only [V2.beq, Bool.and_eq_true, beq_iff_eq] at hb
  rw [hb.1, hb.2]

theorem pts_xpv : ∀ p ∈ x0Pts, v2N p ∈ xPV := fun p hp => by
  rw [← pts_map]
  exact List.mem_map_of_mem hp

theorem xpts_k1 : (List.eraseDups xPV).length = 14 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem xpts_k2 : (XPTS.all fun v => Nat.beq (vecJ rm v (getN one XG 0)) v) = true := by quickRfl

theorem xpts_k3 : (xPV.filter fun v => Nat.beq v (v2N rootV)).length = 480 :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem pts_ok : chkX0Pts = true := by
  have h0 := x0Gen_enc (i := 0) (by decide)
  have e1 := eraseDups_map_inj (f := v2N) _ x0Pts (le_refl _) (fun a _ b _ h => v2N_inj h)
  rw [pts_map] at e1
  have l1 := congrArg List.length e1
  rw [List.length_map, xpts_k1] at l1
  have e3 := filter_map_comm (p := fun p => p.beq rootV) (q := fun v => Nat.beq v (v2N rootV)) (f := v2N)
    x0Pts (fun p _ => beq_v2N p rootV)
  rw [pts_map] at e3
  have l3 := congrArg List.length e3
  rw [List.length_map, xpts_k3] at l3
  have a2 : (x0Pts.all fun p => (frApply (frTable (x0GenRows[0]!)) p).beq p) = true := by
    refine List.all_eq_true.2 fun p hp => ?_
    have hm := pts_xpv p hp
    unfold xPV at hm
    obtain ⟨k, hk, hkk⟩ := List.mem_map.1 hm
    have hd := xDer_spec (List.mem_range.1 hk)
    unfold xDerK at hd
    simp only [andB_eq, Bool.and_eq_true] at hd
    have hmem : v2N p ∈ XPTS := by
      rw [← hkk]
      exact getN_mem 0 XPTS _ (lt_of_blt hd.1.1)
    rw [beq_v2N, v2N_frApply hK h0.1 (pts_wf p hp), h0.2]
    exact List.all_eq_true.1 xpts_k2 _ hmem
  unfold chkX0Pts
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨l1.symm, a2⟩, l3⟩

end CertificateChecks.KernelJ4Q

end

module

public import Certificates.Kernel.Fi22.Bray
public import CFSG.Certificates.Kernel.Fi22KillSound
public import CFSG.Certificates.Kernel.Fi22.Bound2.Data.M
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.O
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.Pair
import CFSG.Certificates.Kernel.Fi22.Bound.Checks.O
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.Certificates CFSG.Certificates.LCE
  CertificateChecks.KernelCo2

theorem root_rel {U m k : ℕ} (hk : k < 13) (hb : Nat.beq (Fi22B.rel k) (commPow U m) = true)
    (he : HO.entOK U (nat_lit 254) (nat_lit 510) = true)
    (hwf : Nat.blt (wWord (commEnt U)) (2 ^ (8 * wLen (commEnt U))) = true)
    (hm : Nat.blt (m * wLen (commEnt U)) 1024 = true) :
    ((tg 0)⁻¹ * (bval tg (wWord U) (wLen U))⁻¹ * tg 0 * bval tg (wWord U) (wLen U)) ^ m = 1 := by
  have hv := rel_val k hk
  rw [Nat.eq_of_beq_eq_true hb, show commPow U m = powEnt (commEnt U) m from rfl,
    HO.bval_powEnt tg (by simpa using hwf) (by simpa using hm), HO.bval_commEnt tg he] at hv
  exact hv

theorem pi_rel : ∀ r < 27, bval (fun k => bval tg (wWord (eAB (k + 1))) (wLen (eAB (k + 1))))
    (wWord (CFSG.KD.Fi22KM.XRs r)) (wLen (CFSG.KD.Fi22KM.XRs r)) = 1 := by
  obtain ⟨rep, h0, hw⟩ := bray_walk
  have hcent : ∀ x ∈ HB, x * tg 0 = tg 0 * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (a_cent hx) (tg 0) rfl).symm
  have hsub : ∀ j, HO.entOK (Fi22B.sub j) (nat_lit 4) (nat_lit 17) = true ∧
      bval tg (wWord (Fi22B.sub j)) (wLen (Fi22B.sub j)) ∈ HB := by
    intro j
    by_cases hj : j < 7
    · refine ⟨by interval_cases j <;> quickRfl, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩
    · rw [sub_ge (by omega)]
      exact ⟨by quickRfl, HB.one_mem⟩
  have hU0 := root_rel (k := 4) (by norm_num) CFSG.KD.Fi22BO.rel1 (by quickRfl) (by quickRfl) (by quickRfl)
  have hU1 := root_rel (k := 7) (by norm_num) CFSG.KD.Fi22BO.rel2 (by quickRfl) (by quickRfl) (by quickRfl)
  have key := fun {XRk i j m w R1 c ρ hl hn R2 : ℕ} (hargs : Fi22Kill.pairArgsOK i j w hn = true)
      (h : pairOK CFSG.KD.Fi22BP.blk (nat_lit 82571) CFSG.KD.Fi22BO.UW0 CFSG.KD.Fi22BO.UW1
        XRk i j m w R1 c ρ hl hn R2 = true) =>
    Fi22Kill.pairOK_sound tg HB rep h0 hw hsub hcent a_sq (by quickRfl) ⟨by quickRfl, hU0⟩
      ⟨by quickRfl, hU1⟩ hargs h
  intro r hr
  interval_cases r
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr0
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr1
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr2
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr3
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr4
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr5
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr6
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr7
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr8
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr9
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr10
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr11
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr12
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr13
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr14
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr15
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr16
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr17
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr18
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr19
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr20
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr21
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr22
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr23
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr24
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr25
  · exact key (by quickRfl) CFSG.KD.Fi22KM.pr26

end CertificateChecks.KernelFi22

end

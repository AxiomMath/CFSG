module

public import Certificates.Kernel.SporSch.HN.C13608G
public import Certificates.Kernel.SporSch.HN.Pt2085
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q0
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q1
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q2
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q3
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q4
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q5
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q6
public import Certificates.Kernel.SporSch.HN.FixK.D13608Q7
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q0
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q1
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q2
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q3
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q4
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q5
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q6
public import Certificates.Kernel.SporSch.HN.FixK.F13608Q7
public import CFSG.Sporadic.HNSchreier.LocalOuter
public import CFSG.Sporadic.HNSchreier.VectorData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN13608

open CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CertificateChecks.KernelSporSch.HNPt2109
open CFSG.KD.HN13608 CFSG.KD.LgHNX CFSG.KD.HNXK Matrix

theorem dotSum_of {k lo' n' : ℕ} (h : dot13608 k = true) (h1 : 2227 * k = lo')
    (h2 : fixLen k = n') : dotSum TX CM3 M MR L1 ONES GQ 1 lo' n' = DOT13608 k := by
  subst h1 h2
  exact Nat.eq_of_beq_eq_true h

theorem dot_total :
    ∑ b ∈ Finset.range 17813, dotLeaf TX CM3 M MR L1 ONES GQ 1 b (hnxC b) = 166459 := by
  have z : ∑ b ∈ Finset.range 0, dotLeaf TX CM3 M MR L1 ONES GQ 1 b (hnxC b) = 0 := rfl
  have s0 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_0.c0 (lo' := 0) (n' := 2227) (by decide) (by decide)) z
  have s1 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_1.c0 (lo' := 2227) (n' := 2227) (by decide) (by decide)) s0
  have s2 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_2.c0 (lo' := 4454) (n' := 2227) (by decide) (by decide)) s1
  have s3 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_3.c0 (lo' := 6681) (n' := 2227) (by decide) (by decide)) s2
  have s4 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_4.c0 (lo' := 8908) (n' := 2227) (by decide) (by decide)) s3
  have s5 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_5.c0 (lo' := 11135) (n' := 2227) (by decide) (by decide)) s4
  have s6 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_6.c0 (lo' := 13362) (n' := 2227) (by decide) (by decide)) s5
  have s7 := HNXP.dotSum_add TX CM3 M MR L1 ONES GQ 1
    (dotSum_of D13608_7.c0 (lo' := 15589) (n' := 2224) (by decide) (by decide)) s6
  exact s7.trans (by decide +kernel)

theorem fix_total :
    ∑ b ∈ Finset.range 17813, fixLeaf TX 464 CM3 M [GE] b (hnxC b) = 50 :=
  (sum8 (fixSum_of F13608_0.c0 (lo' := 0) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_1.c0 (lo' := 2227) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_2.c0 (lo' := 4454) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_3.c0 (lo' := 6681) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_4.c0 (lo' := 8908) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_5.c0 (lo' := 11135) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_6.c0 (lo' := 13362) (n' := 2227) (by decide) (by decide))
    (fixSum_of F13608_7.c0 (lo' := 15589) (n' := 2224) (by decide) (by decide))).trans
    (by decide +kernel)

theorem ncard_X {p : X → Prop} {q : ℕ → Prop} [DecidablePred q] (h : ∀ x : X, p x ↔ q x.val) :
    {x : X | p x}.ncard = ((Finset.range nPts).filter q).card := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_congr (fun x _ => x.val) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    exact ⟨x.isLt, (h x).1 hx⟩
  · intro a b _ _ hab
    exact Fin.ext hab
  · intro b hb
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hb
    exact ⟨⟨b, hb.1⟩, (h ⟨b, hb.1⟩).2 hb.2, rfl⟩

open Certificates in
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native Matrix in
theorem facts : {x : X | PK x.val ⬝ᵥ ((formM * (matJ (aJ * ((aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ *
      aJ * bJ * aJ)⁻¹ * bJ * (aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ))) +
      matJ (aJ * ((aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ)⁻¹ * bJ *
      (aJ * bJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ * bJ * aJ))) ^ 2)) *ᵥ PK x.val) = 1}.ncard =
      166459 ∧
    {x : X | hWordJ [2, 4, 5, 8, 5, 4, 2] • x = x}.ncard = 50 := by
  refine ⟨?_, ?_⟩
  · rw [← card_dot_of dot_total]
    exact ncard_X fun x => Iff.rfl
  · rw [← card_fix_e_of fix_total]
    refine ncard_X fun x => ?_
    rw [HNPt2085.wJ_sL _ (by decide), gi_of_lt _ x.isLt]
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

end CertificateChecks.KernelSporSch.HN13608

end

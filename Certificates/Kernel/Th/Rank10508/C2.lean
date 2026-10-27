module

public import Certificates.Kernel.Th.Rank10508.C1
public import Certificates.Kernel.Th.Rank10508.C2Checks
public import Certificates.Kernel.Th.Max3
import all Certificates.Kernel.Th.Max3
public import CFSG.Certificates.Kernel.Th.Max3S.R10508

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh.Rank10508

open CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.Rank CFSG.KC.ThRk10508 CFSG.KC.Th.Max3S
open CFSG.KD.ThRk10508

private theorem eRB : max3Data.ThM3_RB = CFSG.KD.ThM3.RB := rfl

private theorem ec : max3Data.ThS_c = CFSG.KD.ThS.c := rfl

private theorem erm : max3Data.ThS_rm = CFSG.KD.ThS.rm := rfl

private theorem eONE : max3Data.ThS_ONE = CFSG.KD.ThS.ONE := rfl

theorem hcq : ∀ g < 8, cqChunk max3Data.ThM3_RB max3Data.ThS_c max3Data.ThS_rm Cl g = true := by
  rw [eRB, ec, erm]
  intro g hg
  interval_cases g
  exacts [ch10508cq0, ch10508cq1, ch10508cq2, ch10508cq3, ch10508cq4, ch10508cq5, ch10508cq6,
    ch10508cq7]

theorem hcc : ∀ j < Cl.length,
    ccK max3Data.ThM3_RB max3Data.ThS_c max3Data.ThS_rm Cl (getN Cl j) = true := by
  rw [eRB, ec, erm]
  intro j hj
  have hj' : j < 16 := by simpa [Cl] using hj
  interval_cases j
  exacts [ch10508cc0, ch10508cc1, ch10508cc2, ch10508cc3, ch10508cc4, ch10508cc5, ch10508cc6,
    ch10508cc7, ch10508cc8, ch10508cc9, ch10508cc10, ch10508cc11, ch10508cc12, ch10508cc13,
    ch10508cc14, ch10508cc15]

theorem hrow : ∀ i : Fin 12, rowI max3Data.ThM3_RB max3Data.ThS_c max3Data.ThS_rm max3Data.ThS_ONE
    LB Ks Es Ws Cl Ds Ts i.val = true := by
  rw [eRB, ec, erm, eONE]
  rintro ⟨i, hi⟩
  interval_cases i
  exacts [ch10508row0, ch10508row1, ch10508row2, ch10508row3, ch10508row4, ch10508row5,
    ch10508row6, ch10508row7, ch10508row8, ch10508row9, ch10508row10, ch10508row11]

theorem hKs : ∀ i : Fin 12, getN Ks i.val = (rkK0 i).val := by decide +kernel

theorem hEs : ∀ i : Fin 12, getN Es i.val = encGen (rkWord i) := by decide +kernel

theorem hWs : ∀ i : Fin 12, getN Ws i.val = (rkWord i).length := by decide +kernel

theorem hTs : ∀ i : Fin 12, rkTypeB i = false → memL Ts i.val = false := by decide +kernel

@[expose] def C0F : List (Fin 512) :=
  [0, 1, 24, 25, 160, 161, 184, 185, 326, 327, 350, 351, 486, 487, 510, 511]

theorem hC0 : rkC0 Cl = C0F := by decide +kernel

theorem hD0 (i : Fin 12) : rkD0 Cl Ds i = C0F.filter fun k => memL (getL Ds i.val) k.val := by
  rw [rkD0, hC0]

theorem h16 : (rkC0 Cl).length = 16 := by rw [hC0]; rfl

theorem h8F : ∀ i : Fin 12, (C0F.filter fun k => memL (getL Ds i.val) k.val).length ≤ 8 := by
  decide +kernel

theorem h8 (i : Fin 12) : (rkD0 Cl Ds i).length ≤ 8 := by
  rw [hD0]
  exact h8F i

theorem h4dec : ∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
    ((C0F.filter fun k => memL (getL Ds i.val) k.val).filter fun k =>
      decide (k ∈ C0F.filter fun k => memL (getL Ds j.val) k.val)).length ≤ 4 ∨
      (∀ t, rkP j t = rkP i t) ∨ (∀ t, rkP j t = rkP i (aPerm t)) := by
  decide +kernel

theorem h4 : ∀ i j : Fin 12, rkTypeB i = true → rkTypeB j = true →
    rkPerm i * rkPerm j = rkPerm j * rkPerm i → rkPerm j ≠ rkPerm i →
    rkPerm j ≠ rkPerm i * aPerm →
    ((rkD0 Cl Ds i).filter fun k => decide (k ∈ rkD0 Cl Ds j)).length ≤ 4 := by
  intro i j hi hj _ hne hne'
  rw [hD0 i, hD0 j]
  rcases h4dec i j hi hj with h | h | h
  · exact h
  · refine absurd (Equiv.ext fun t => ?_) hne
    rw [rkP_eq, rkP_eq]
    exact h t
  · refine absurd (Equiv.ext fun t => ?_) hne'
    rw [Equiv.Perm.mul_apply, rkP_eq, rkP_eq]
    exact h t

end CertificateChecks.KernelTh.Rank10508

end

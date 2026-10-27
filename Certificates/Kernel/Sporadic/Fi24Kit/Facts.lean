module

public import Certificates.Kernel.Sporadic.Fi24Kit.Checks
public import Certificates.Kernel.Sporadic.Fi24Net.Letters
public import CFSG.Certificates.Kernel.Spor.Fi24KitSound

public section

namespace CFSG.KD.Fi24Kit

open CFSG.KC CFSG.KC.Fi24Net CFSG.KS.Fi24Net CFSG.KS.Fi24Kit CFSG.KD.Fi24Net

theorem NW_nv {j : Nat} (hj : j < 13) : NV (NW j) := (net_spec (nck_spec j hj)).1

theorem WV_of {w : List Nat} (h : ∀ l ∈ w, l < 26) : WV NW w :=
  fun l hl => NW_nv (by have := h l hl; omega)

theorem wA_lt : ∀ l ∈ wA, l < 26 := by decide

theorem wB_lt : ∀ l ∈ wB, l < 26 := by decide

theorem tck_all : ∀ k < 19, tck k = true := by
  intro k hk
  interval_cases k
  exacts [Ck.t0, Ck.t1, Ck.t2, Ck.t3, Ck.t4, Ck.t5, Ck.t6, Ck.t7, Ck.t8, Ck.t9, Ck.t10, Ck.t11,
    Ck.t12, Ck.t13, Ck.t14, Ck.t15, Ck.t16, Ck.t17, Ck.t18]

theorem tP_facts : NV NT ∧ pF NT 0 = 0 ∧ (∀ x < 306936, pF NT x < 306936) ∧
    ∀ x < 306936,
      pF NT (CFSG.KC.Fi24Orb.oA (CFSG.KD.Fi24Orb.OL x)) = wN NW wA (pF NT x) ∧
      pF NT (CFSG.KC.Fi24Orb.oB (CFSG.KD.Fi24Orb.OL x)) = wN NW wB (pF NT x) := by
  obtain ⟨hT, hpt⟩ := net_spec Ck.n
  have h0 : pF NT 0 = 0 := by
    rw [← CFSG.KS.Fi24NetPt.ptF_eq]
    exact Nat.eq_of_beq_eq_true Ck.z
  refine ⟨hT, h0, fun x hx => (hpt x (by omega)).2 hx, fun x hx => ?_⟩
  have hab := gens_spec nck_spec gck_spec hx
  have key := tp_spec hT (NW_nv (by decide)) (NW_nv (by decide)) (WV_of wA_lt) (WV_of wB_lt)
    tck_all x (by omega)
  change pF NT (pF (NW 0) x) = _ ∧ pF NT (pF (NW 1) x) = _ at key
  rw [hab.1, hab.2] at key
  exact key

end CFSG.KD.Fi24Kit

end

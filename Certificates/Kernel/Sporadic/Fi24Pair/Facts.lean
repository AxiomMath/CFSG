module

public import Certificates.Kernel.Sporadic.Fi24Pair.ChecksB
public import Certificates.Kernel.Sporadic.Fi24Pair.SigP
public import CFSG.Certificates.Kernel.Spor.Fi24PairPSound
public import Certificates.Kernel.Sporadic.Fi24Kit.Facts

public section

namespace CFSG.KD.Fi24Pair

open CFSG.KC.Fi24Pair

theorem fp_r0 : FP r0 = 254589 := by decide

theorem fp_r1 : FP r1 = 61582 := by decide

theorem NL_mem : ∀ N ∈ NL, ∃ k < 18, N = NT k := by
  intro N hN
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hN
  exact ⟨k, List.mem_range.1 hk, rfl⟩

theorem sig_facts : ∀ k < 18, SigF LRn FP (NT k) (4 + k) := by
  intro k hk
  have hc : CFSG.KC.Fi24PairP.cfOK CF FP = true := CkP.cfc_t
  have hCF : CFSG.KS.Fi24Net.NV CF :=
    CFSG.KS.Fi24Net.nv_of_masksOK (CFSG.KC.Benes.andB_true hc).1
  have hFP : ∀ p < 3240, FP p < 524288 := fun p hp => by
    have := (fOK_spec CkB.pts_t).1 p hp
    omega
  have h := CFSG.KC.Fi24PairP.sigP_spec hCF
    (CFSG.KD.Fi24Kit.NW_nv (by change (8 + k) / 2 < 13; omega)) hFP hc (CkP.sgp_all k hk)
  refine ⟨h.1, fun p hp => ⟨(h.2 p hp).1, ?_⟩⟩
  have e : LRn (4 + k) (FP p) = CFSG.KS.Fi24Net.LN CFSG.KD.Fi24Net.NW (8 + k) (FP p) := by
    unfold LRn
    rw [CFSG.KS.Fi24NetPt.letN_eq]
    congr 1
    change 4 + k + 4 = 8 + k
    omega
  rw [e]
  exact (h.2 p hp).2

theorem pair_orbit {G : Type*} [Group G] [MulAction G (Fin 306936)] (g : ℕ → G)
    (hg : ∀ k < 18, ∀ x : Fin 306936,
      ((g k) • x).val = CFSG.KS.Fi24Net.LN CFSG.KD.Fi24Net.NW (8 + k) x.val)
    (c0 c1 : Fin 306936) (hc0 : c0.val = 254589) (hc1 : c1.val = 61582) :
    3499200 ≤ Nat.card (MulAction.orbit (letH g) ((c0, c1) : Fin 306936 × Fin 306936)) ∧
      ∀ j < 6, ∀ h ∈ letH g, ¬((h • c0).val = (outP j).1 ∧ (h • c1).val = (outP j).2.2.1) := by
  have hg' : ∀ k < 18, ∀ x : Fin 306936, ((g k) • x).val = LRn (4 + k) x.val := by
    intro k hk x
    have e : LRn (4 + k) x.val = CFSG.KS.Fi24Net.LN CFSG.KD.Fi24Net.NW (8 + k) x.val := by
      unfold LRn
      rw [CFSG.KS.Fi24NetPt.letN_eq]
      congr 1
      change 4 + k + 4 = 8 + k
      omega
    rw [e]
    exact hg k hk x
  have hw0 : hOK (hW0.reverse.map NT) (HT 0) r0 = true := by
    rw [List.map_reverse]
    exact CkB.hw0_t
  have hw1 : hOK (hW1.reverse.map NT) (HT 1) r0 = true := by
    rw [List.map_reverse]
    exact CkB.hw1_t
  have key := pair_facts (LR := LRn) (FP := FP) (NT := NT) g hg'
    (fun k hk => CkB.clo_all k hk) sig_facts CkB.pts_t CkB.reg_t NL_mem
    (Nat.eq_of_beq_eq_true CkB.orb0_t) (by decide) (by decide) hw0 hw1
    (Nat.eq_of_beq_eq_true CkB.orb1_t) c0 c1 (hc0.trans fp_r0.symm) (hc1.trans fp_r1.symm)
  exact ⟨key.1, fun j hj h hh => key.2 (CkB.out_all j hj) h hh⟩

end CFSG.KD.Fi24Pair

end

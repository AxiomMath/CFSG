module

public import Certificates.Kernel.S1277.SvBranch
public import CFSG.Certificates.Kernel.S1277KFacts
public import Certificates.Kernel.S1277.Fr
public import Certificates.Kernel.S1277.Lat
public import Certificates.Kernel.S1277.SvGlue
public import Certificates.Kernel.S1277.Vl

public section

namespace CFSG.KP.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sv CFSG.KC.S1277Sig CFSG.KC.S1277Fr
  CFSG.KC.S1277Vl CFSG.KD.S1277Fr CFSG.KD.S1277Sv CFSG.KD.S1277Lat CFSG.KD.S1277Mod
  CFSG.KD.S1277Vl CFSG.KS.S1277Lat CFSG.KS.S1277Sig CFSG.KS.S1277Sv CFSG.KS.S1277Fr
  CFSG.KS.S1277Vl CFSG.KS.S1277Ar CFSG.KS.S1277Cand CFSG.KS.S1277Facts CFSG.Quasithin.H13.I1277
  CFSG.Open Certificates.Data.S1277Sig Certificates.Data.S1277Facts

theorem survFacts_n {G : Type} [Group G] [Finite G] {H K Q : Subgroup G} {κ : G → ℕ}
    (hKH : K ≤ H) (hQK : Q ≤ K) (hQn : ∀ h ∈ H, ∀ x ∈ Q, h * x * h⁻¹ ∈ Q)
    (hκ : MCod K Mn κ) {z : G} (hzH : ∀ h ∈ H, h * z * h⁻¹ = z) (hzK : z ∈ K)
    (hzc : κ z = onen * 64 + 5)
    (hQN : ∀ n, (∃ q ∈ Q, κ q = n) ↔ (nmn.getD 14 0).testBit n = true) : SurvFacts H K Q z := by
  classical
  obtain ⟨hil, hd6, hnl⟩ := sv_idx
  obtain ⟨hi14, hnx⟩ := CFSG.KP.S1277Vl.vl_nx
  have hN := nodesChk_spec CFSG.KP.S1277Lat.nodes_n 14 (by rw [hnl]; norm_num)
  have hfrl := frAll_spec (j := 4) CFSG.KP.S1277Fr.fr_n (by rw [hil]; norm_num)
  rw [hi14, hd6, ← hzc] at hfrl
  obtain ⟨hfr, hl⟩ := hfrl
  have hcod := codQ_of hκ hN hQK hQN hfr
  have hlab := labInv_of hκ hN hQK hQN hfr hzK hzH hQn hl
  have hQc : Nat.card Q = 2 ^ 7 := by
    rw [← hnx]
    exact card_of_node hκ CFSG.KP.S1277Lat.gen_n CFSG.KP.S1277Lat.nodes_n (by rw [hnl]; norm_num)
      hQK hQN
  have hKcard : Nat.card K = 48 * 64 := card_K hκ
  obtain ⟨hzΦ, hΦ, hz1, hcen, hcm⟩ := e_sound hκ hN hQK hQN hfr CFSG.KP.S1277Vl.vl_e hzK hzc
  unfold SurvFacts
  refine ⟨_, φL (sgln.getD 4 0), hcod, hlab, hQc, hzΦ, hΦ, hz1, hcen, hcm, ?_⟩
  intro D hDw m hm hm2 hm1
  have hD : ∀ x, D.wc x = rd6 (sgcn.getD 4 0) (κ x) := hDw
  have hR : D.rho.range ≤ Sig 6 (φL (sgln.getD 4 0)) :=
    D.range_le_Sig (φL (sgln.getD 4 0)) (fun x => φL (sgln.getD 4 0) (rd6 (sgcn.getD 4 0) (κ x)))
      (fun x _ => by rw [hD]) (fun h hh x hx => hlab h hh x hx)
  have hRc : Nat.card D.rho.range = 24 * m := by
    rw [hQc, hKcard] at hm
    omega
  have hsg : ∀ g ∈ sg, pkSet D.rho.range g :=
    sgChk_mem hκ hKH hQK hQN hfr D hD CFSG.KP.S1277Lat.gen_n sv_sg
  have key : ∀ (a ap aj ad : List ℕ) (k ty : ℕ) (b : List (List ℕ)),
      aChk1 sg sl vg vt k ty a ap aj ad = true →
      vlChk a (b.getD 0 []) (b.getD 1 []) = true →
      abChk Mn (ntn.getD 14 []) (sgcn.getD 4 0) (b.getD 0 []) = true →
      abChk Mn (ntn.getD 14 []) (sgcn.getD 4 0) (b.getD 1 []) = true →
      (∀ y, pkSet D.rho.range y ↔ y ∈ a) →
      ImFacts Q (fun g => rd6 (sgcn.getD 4 0) (κ g)) D.rho.range := by
    intro a ap aj ad k ty b ha hv habu habv hS
    rw [aChk1] at ha
    simp only [Bool.and_eq_true] at ha
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hlen⟩, hinc⟩, -⟩, -⟩ := ha
    exact imFacts_of hκ hN hQK hQN D hD hR (incL_nodup a 0 hinc).2 (Nat.eq_of_beq_eq_true hlen)
      hS hv habu habv
  rcases sv_R hR hRc hm2 hm1 hsg with hS | hS
  · exact key a1 a1p a1j a1d k1 2 b1 sv_a1 CFSG.KP.S1277Vl.vl_a1 CFSG.KP.S1277Vl.vl_ab1.1
      CFSG.KP.S1277Vl.vl_ab1.2 hS
  · exact key a2 a2p a2j a2d k2 3 b2 sv_a2 CFSG.KP.S1277Vl.vl_a2 CFSG.KP.S1277Vl.vl_ab2.1
      CFSG.KP.S1277Vl.vl_ab2.2 hS

end CFSG.KP.S1277Sv

end

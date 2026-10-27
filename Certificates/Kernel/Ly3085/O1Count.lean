
module

public import Certificates.Kernel.Ly3085.ChartGlue
public import Certificates.Kernel.Ly3085.Omega.O1K
public import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CFSG.KD.LyO1

#kc_forall_chunks nodesOK (fun b => CFSG.KC.LyOm.cRange BC KX PT WT GT WC nc n b 1 = true) 306
  CFSG.KD.LyO1.o1 1

#kc_forall_chunks sortsOK (fun k => CFSG.KC.LyOm.cSort KX PT SG n (1024 * k) 1024 = true) 19
  CFSG.KD.LyO1.o1s 1

theorem n_eq : n = 19530 := by decide +kernel

theorem nc_eq : nc = 8 := by decide +kernel

end CFSG.KD.LyO1

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open Matrix MulAction

theorem o1_gt : ∀ s < 2, ∀ c < CFSG.KD.LyO1.nc, ∀ c' < CFSG.KD.LyO1.nc,
    fVld CFSG.KD.LyOm.BC (CFSG.KD.LyO1.GT (s + 2 * c + 16 * c')) = true ∧
    Nat.beq (fMul CFSG.KD.LyOm.BC (CFSG.KD.LyO1.PI c) (CFSG.KD.LyO1.GT (s + 2 * c + 16 * c')))
      (fMul CFSG.KD.LyOm.BC (pickL [CFSG.KD.LyOm.P0, CFSG.KD.LyOm.P1] s) (CFSG.KD.LyO1.PI c')) =
        true := by
  intro s hs c hc c' hc'
  have hc8 : c < 8 := by rw [← CFSG.KD.LyO1.nc_eq]; exact hc
  have hc8' : c' < 8 := by rw [← CFSG.KD.LyO1.nc_eq]; exact hc'
  have e1 : (s + 2 * c + 16 * c') / 2 % 8 = c := by omega
  have e2 : (s + 2 * c + 16 * c') / 16 = c' := by omega
  have e3 : (s + 2 * c + 16 * c') % 2 = s := by omega
  have key : ∀ lo, tabGT CFSG.KD.LyOm.BC CFSG.KD.LyO1.PI CFSG.KD.LyO1.GT CFSG.KD.LyOm.P0
      CFSG.KD.LyOm.P1 CFSG.KD.LyO1.nc lo 32 = true → lo ≤ s + 2 * c + 16 * c' →
      s + 2 * c + 16 * c' < lo + 32 →
      fVld CFSG.KD.LyOm.BC (CFSG.KD.LyO1.GT (s + 2 * c + 16 * c')) = true ∧
      Nat.beq (fMul CFSG.KD.LyOm.BC (CFSG.KD.LyO1.PI ((s + 2 * c + 16 * c') / 2 % 8))
        (CFSG.KD.LyO1.GT (s + 2 * c + 16 * c')))
        (fMul CFSG.KD.LyOm.BC (pickL [CFSG.KD.LyOm.P0, CFSG.KD.LyOm.P1] ((s + 2 * c + 16 * c') % 2))
          (CFSG.KD.LyO1.PI ((s + 2 * c + 16 * c') / 16))) = true := fun lo h h1 h2 =>
    tabGT_sound h _ h1 h2 (by rw [e1]; exact hc) (by rw [e2]; exact hc')
  have r : fVld CFSG.KD.LyOm.BC (CFSG.KD.LyO1.GT (s + 2 * c + 16 * c')) = true ∧
      Nat.beq (fMul CFSG.KD.LyOm.BC (CFSG.KD.LyO1.PI ((s + 2 * c + 16 * c') / 2 % 8))
        (CFSG.KD.LyO1.GT (s + 2 * c + 16 * c')))
        (fMul CFSG.KD.LyOm.BC (pickL [CFSG.KD.LyOm.P0, CFSG.KD.LyOm.P1] ((s + 2 * c + 16 * c') % 2))
          (CFSG.KD.LyO1.PI ((s + 2 * c + 16 * c') / 16))) = true := by
    by_cases k1 : s + 2 * c + 16 * c' < 32
    · exact key 0 CFSG.KD.LyOm.o1gt0 (by omega) (by omega)
    by_cases k2 : s + 2 * c + 16 * c' < 64
    · exact key 32 CFSG.KD.LyOm.o1gt1 (by omega) (by omega)
    by_cases k3 : s + 2 * c + 16 * c' < 96
    · exact key 64 CFSG.KD.LyOm.o1gt2 (by omega) (by omega)
    · exact key 96 CFSG.KD.LyOm.o1gt3 (by omega) (by omega)
  rw [e1, e2, e3] at r
  exact r

theorem o1_sort {k : ℕ} (hk : k + 1 < 19530) :
    getRec CFSG.KD.LyO1.SG 20 k < CFSG.KD.LyO1.n ∧
      getRec CFSG.KD.LyO1.SG 20 (k + 1) < CFSG.KD.LyO1.n ∧
      cKey CFSG.KD.LyO1.KX CFSG.KD.LyO1.PT (getRec CFSG.KD.LyO1.SG 20 k) <
        cKey CFSG.KD.LyO1.KX CFSG.KD.LyO1.PT (getRec CFSG.KD.LyO1.SG 20 (k + 1)) := by
  by_cases hl : k < 19456
  · exact cSort_sound (CFSG.KD.LyO1.sortsOK (k / 1024) (by change k / 1024 < 19; omega)) k
      (by omega) (by omega)
  · exact cSort_sound CFSG.KD.LyO1.o1s19 k (by change 19456 ≤ k; omega)
      (by change k < 19456 + 73; omega)

theorem o1_tree
    [LySeed] :
    (∀ i < CFSG.KD.LyO1.n, LCanon 12 7 111 (getRec CFSG.KD.LyO1.KX 9324 i) ∧
      chartOf (getRec CFSG.KD.LyO1.PT 32 i) < CFSG.KD.LyO1.nc ∧
      lastCols (blkM (getRec CFSG.KD.LyO1.KX 9324 i)) = 1) ∧
    (∀ i < CFSG.KD.LyO1.n, (⟨rs (blkM (getRec CFSG.KD.LyO1.KX 9324 i) *
      bigM (CFSG.KD.LyO1.PJ (chartOf (getRec CFSG.KD.LyO1.PT 32 i))) * TIm)⟩ : LySp) ∈
        orbit lyH (imOp (gRep 1 • opE))) ∧
    (∀ i < CFSG.KD.LyO1.n, ∀ j < CFSG.KD.LyO1.n,
      rs (blkM (getRec CFSG.KD.LyO1.KX 9324 i) *
        bigM (CFSG.KD.LyO1.PJ (chartOf (getRec CFSG.KD.LyO1.PT 32 i))) * TIm) =
      rs (blkM (getRec CFSG.KD.LyO1.KX 9324 j) *
        bigM (CFSG.KD.LyO1.PJ (chartOf (getRec CFSG.KD.LyO1.PT 32 j))) * TIm) → i = j) := by
  have hn : 0 < CFSG.KD.LyO1.n := by rw [CFSG.KD.LyO1.n_eq]; norm_num
  have hnc : CFSG.KD.LyO1.nc ≤ 8 := by rw [CFSG.KD.LyO1.nc_eq]
  obtain ⟨cP0, cP1, cPI0, cPI1, e0, -, e1, -⟩ := p_facts
  obtain ⟨hcan, hstep, hinj⟩ := chart_tree (KX := CFSG.KD.LyO1.KX) (PT := CFSG.KD.LyO1.PT)
    (WT := CFSG.KD.LyO1.WT) (GT := CFSG.KD.LyO1.GT) (WC := CFSG.KD.LyO1.WC)
    (PI := CFSG.KD.LyO1.PI) (PJ := CFSG.KD.LyO1.PJ) (SG := CFSG.KD.LyO1.SG) (n := CFSG.KD.LyO1.n)
    (nc := CFSG.KD.LyO1.nc) (G0 := CFSG.KD.LyOm.P0) (G1 := CFSG.KD.LyOm.P1)
    (Gi0 := bigM CFSG.KD.LyOm.PI0) (Gi1 := bigM CFSG.KD.LyOm.PI1) hnc ⟨cP0, cP1⟩
    ⟨by rw [← (fmul cP0 cPI0).2, beq_eq CFSG.KD.LyOm.pi0, one_facts.2],
      by rw [← (fmul cP1 cPI1).2, beq_eq CFSG.KD.LyOm.pi1, one_facts.2]⟩
    CFSG.KD.LyOm.o1pi o1_gt CFSG.KD.LyOm.o1wc
    (fun i hi => cRange_sound (CFSG.KD.LyO1.nodesOK (i / 64) (by
      rw [CFSG.KD.LyO1.n_eq] at hi
      change i / 64 < 306
      omega)) i (by omega) (by omega) hi)
    (fun k hk => by
      have hk' := hk
      rw [CFSG.KD.LyO1.n_eq] at hk'
      by_cases hm : k + 1 < 19530
      · exact (o1_sort hm).1
      · have : k = 19528 + 1 := by omega
        rw [this]
        exact (o1_sort (k := 19528) (by norm_num)).2.1)
    (fun k hk => by
      rw [CFSG.KD.LyO1.n_eq] at hk
      exact (o1_sort hk).2.2)
  obtain ⟨cUT, eUT, -⟩ := rep1
  have hroot := root_space (hcan 0 hn) CFSG.KD.LyOm.o1pi hnc cUT eUT CFSG.KD.LyOm.o1root
  let sp : ℕ → LySp := fun i => ⟨rs (blkM (getRec CFSG.KD.LyO1.KX 9324 i) *
    bigM (CFSG.KD.LyO1.PJ (chartOf (getRec CFSG.KD.LyO1.PT 32 i))) * TIm)⟩
  have hgen : ∀ s < 2, aStar (s + 2) ∈ lyH ∧
      Tm * bigM (pickL [CFSG.KD.LyOm.P0, CFSG.KD.LyOm.P1] s) * TIm = (mat (aStar (s + 2)))ᵀ := by
    intro s hs
    refine ⟨aStar_mem_lyH (by omega), ?_⟩
    interval_cases s
    · exact e0
    · exact e1
  have hmem : ∀ i < CFSG.KD.LyO1.n, sp i ∈ orbit lyH (imOp (gRep 1 • opE)) := by
    refine mem_orbit_of_tree (G := lyH) _ sp (fun i => fldW (getRec CFSG.KD.LyO1.PT 32 i) 0 20) _
      ?_ fun i hi0 hi => ?_
    · rw [imOp_smul_opE]
      exact LySp.ext hroot
    · obtain ⟨hp, hl, he⟩ := hstep i hi hi0
      obtain ⟨hH, hm⟩ := hgen _ hl
      refine ⟨hp, ⟨aStar (fldW (getRec CFSG.KD.LyO1.PT 32 i) 20 4 + 2), hH⟩, ?_⟩
      change sp i = aStar (fldW (getRec CFSG.KD.LyO1.PT 32 i) 20 4 + 2) • sp _
      rw [← step_smul hm]
      exact LySp.ext he
  refine ⟨fun i hi => ⟨(hcan i hi).1, (hcan i hi).2, ?_⟩, hmem, hinj⟩
  have hnode := CFSG.KD.LyO1.nodesOK (i / 64) (by
    have := hi
    rw [CFSG.KD.LyO1.n_eq] at this
    change i / 64 < 306
    omega)
  have hs := cNode_sound' hBC (GT := CFSG.KD.LyO1.GT) (WC := CFSG.KD.LyO1.WC)
    (fun s hs c hc c' hc' => fvld_canon (o1_gt s hs c hc c' hc').1)
    (fun e c hec hc => fvld_canon ((tabWC_sound CFSG.KD.LyOm.o1wc) e c hec hc hnc).1)
    (fun j hj => hcan j (by omega)) (cRange_sound hnode i (by omega) (by omega) hi)
  exact hs.2.2.1

theorem card_orbit_o1_sp
    [LySeed] : 19530 ≤ Nat.card (orbit lyH (imOp (gRep 1 • opE))) := by
  obtain ⟨-, hmem, hinj⟩ := o1_tree
  have h := card_le_orbit_of_inj (G := lyH) (fun x : LySp => x) (fun _ _ => rfl)
    (imOp (gRep 1 • opE)) CFSG.KD.LyO1.n _ hmem (fun i hi j hj e => hinj i hi j hj (congrArg LySp.V e))
  rw [CFSG.KD.LyO1.n_eq] at h
  exact h

theorem card_orbit_o1
    [LySeed] : 19530 ≤ Nat.card (orbit lyH (gRep 1 • opE)) :=
  card_orbit_o1_sp.trans (card_orbit_le_of_map imOp (imOp_smulS lyH) _)

end CertificateChecks.KernelLy.Omega

end

end

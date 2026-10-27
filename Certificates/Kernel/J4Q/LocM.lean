module

public import Certificates.Kernel.J4Q.LocVec
public import Certificates.Kernel.J4Q.Orbits
public import Certificates.Kernel.J4Q.LocData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.J4.QTRankWitNative

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def MLs : List Nat := [ML_0, ML_1, ML_2, ML_3, ML_4, ML_5]

@[expose] noncomputable def MLIs : List Nat := [MLI_0, MLI_1, MLI_2, MLI_3, MLI_4, MLI_5]

theorem ml_chk : allR 6 (fun i => andB (Nat.beq (getN one MLs i)
    (pathRK c rm one [A, B] (repPaths.getD (1 + 1 * i) [])))
      (andB (canonJ pad (getN one MLIs i)) (Nat.beq (mulJ c rm (getN one MLs i) (getN one MLIs i)) one))) =
    true := by
  quickRfl

theorem evs_chk : eqLK EVS (smapK (fun c => vecEtaK rm Us c (v2N w0)) (rangeK 2048)) = true := by
  quickRfl

theorem EVS_eq : EVS = (List.range 2048).map fun c => vecEtaK rm Us c (v2N w0) := by
  rw [eqLK_spec evs_chk, smapK_eq, rangeK_eq]

theorem zml_chk : eqLK ZML (fstsK (ptsK OR.s1)) = true := by quickRfl

theorem zMasks_ZML : zMasks = ZML := by
  rw [zMasks_eq, eqLK_spec zml_chk]

theorem w0_wf : w0.wf = true := by decide

theorem pathM_enc {i : Nat} (hi : i < 6) : WfA (pathRows (repPaths.getD (1 + 1 * i) [])) ∧
    encR (pathRows (repPaths.getD (1 + 1 * i) [])) = getN one MLs i := by
  have hm := allR_spec ml_chk i hi
  simp only [andB_eq, Bool.and_eq_true] at hm
  obtain ⟨h1, h2⟩ := pathRows_enc (repPaths.getD (1 + 1 * i) [])
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true hm.1).symm⟩

theorem pathMi_enc {i : Nat} (hi : i < 6) : WfA (invRows (pathRows (repPaths.getD (1 + 1 * i) []))) ∧
    encR (invRows (pathRows (repPaths.getD (1 + 1 * i) []))) = getN one MLIs i ∧
    Nat.beq (mulJ c rm (getN one MLs i) (getN one MLIs i)) one = true := by
  have hm := allR_spec ml_chk i hi
  simp only [andB_eq, Bool.and_eq_true] at hm
  have hM := pathM_enc hi
  have := invRows_enc hK hM.1 hm.2.1 (by rw [hM.2]; exact hm.2.2)
  exact ⟨this.1, this.2, hm.2.2⟩

@[expose] noncomputable def cvK (i m : Nat) : Nat :=
  vecJ rm (vecEtaK rm Us m (vecJ rm (v2N w0) (getN one MLs i))) (getN one MLIs i)

theorem conjVec_enc {i : Nat} (hi : i < 6) (m : Nat) :
    (frApply (frTable (mulRows (mulRows (pathRows (repPaths.getD (1 + 1 * i) []))
      (etaRows (uTab (locMats ()) (locInvs ())) 11 m)) (invRows (pathRows (repPaths.getD (1 + 1 * i) [])))))
      w0).wf = true ∧
    v2N (frApply (frTable (mulRows (mulRows (pathRows (repPaths.getD (1 + 1 * i) []))
      (etaRows (uTab (locMats ()) (locInvs ())) 11 m)) (invRows (pathRows (repPaths.getD (1 + 1 * i) [])))))
      w0) = cvK i m := by
  have hM := pathM_enc hi
  have hMi := pathMi_enc hi
  obtain ⟨heta, -⟩ := eta_enc m
  have hx1 := wf_frApply hM.1 w0
  obtain ⟨hx2, hv2⟩ := etaVec_enc hx1 m
  rw [vec_mulRows (wf_mulRows hM.1 heta) hMi.1 w0_wf, vec_mulRows hM.1 heta w0_wf]
  refine ⟨wf_frApply hMi.1 _, ?_⟩
  rw [v2N_frApply hK hMi.1 hx2, hv2, v2N_frApply hK hM.1 w0_wf, hM.2, hMi.2.1]
  rfl

theorem evs_mem {u : V2} (hu : u ∈ (List.range 2048).map (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11)) :
    u.wf = true ∧ v2N u ∈ EVS := by
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hu
  have h' : (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c').wf = true ∧
      v2N (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c') = vecEtaK rm Us c' (v2N w0) :=
    v2N_etaVec hK uTab_enc (by simp [uTab, Us]) w0_wf c'
  obtain ⟨hwu, hvu⟩ := h'
  refine ⟨hwu, ?_⟩
  rw [hvu, EVS_eq]
  exact List.mem_map_of_mem hc'

end CertificateChecks.KernelJ4Q

end

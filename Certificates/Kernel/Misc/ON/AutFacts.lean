module

public import Certificates.Kernel.Misc.ON.Base
public import Certificates.Kernel.Misc.ON.Aut

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple CFSG.KC.Misc.F7 CFSG.KC.Loop

@[expose] noncomputable def initYG : Array Mat45ˣ := (yRegs.map eM).toArray

theorem size_initYG : initYG.size = 9 := by
  simp only [initYG, List.size_toArray, List.length_map]
  rfl

theorem initYG_getD {k : ℕ} (hk : k < 9) : initYG.getD k 1 = eM (yRegs.getD k 0) := by
  have hl : k < yRegs.length := by simp [yRegs]; omega
  rw [initYG, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hl, List.getD_eq_getElem _ _ hl, Option.map_some, Option.getD_some]

theorem initYG_getD_of_ge {k : ℕ} (hk : 9 ≤ k) : initYG.getD k 1 = 1 := by
  have hl : yRegs.length ≤ k := by simp [yRegs]; omega
  rw [initYG, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_none hl, Option.map_none, Option.getD_none]

theorem genProg_length : genProg.length = 15 := by decide +kernel

theorem genProg_idx : ∀ t < 15, opIdxLt (9 + t) (genProg.getD t (.pow 0 0)) = true := by
  decide +kernel

theorem yRegs_lt : ∀ k < 9, yRegs.getD k 0 < 200 := by decide

theorem genTargets_lt : ∀ k < 8, genTargets.getD k 0 < 24 := by decide

theorem mrep_genProg :
    ∀ r < 24, MRep (yrM r) ((runG initYG genProg).getD r 1) ∧
      MRep (yrIM r) ((runG initYG genProg).getD r 1)⁻¹ := by
  have h0 : ∀ r < initYG.size, MRep (yrM r) (initYG.getD r 1) ∧
      MRep (yrIM r) (initYG.getD r 1)⁻¹ := by
    intro r hr
    rw [size_initYG] at hr
    have hb : Nat.blt r 9 = true := by
      rw [Nat.blt_eq]
      exact hr
    have e1 : yrM r = rM (yRegs.getD r 0) := by
      unfold yrM
      rw [hb, nthN_eq, nIf_eq, ite_eq_left rfl]
    have e2 : yrIM r = rIM (yRegs.getD r 0) := by
      unfold yrIM
      rw [hb, nthN_eq, nIf_eq, ite_eq_left rfl]
    rw [e1, e2, initYG_getD hr]
    exact regOKK _ (yRegs_lt r hr)
  have hFI : ∀ r, ∃ B : Mat45, yrIM r = enc B := fun r => by
    unfold yrIM
    cases Nat.blt r 9
    · refine ⟨decC 45 (nthN autIC (Nat.sub r 9)), ?_⟩
      rw [nIf_eq, ite_eq_right Bool.false_ne_true, widen_eq]
    · refine ⟨regIMat (nthN yRegs r), ?_⟩
      rw [nIf_eq, ite_eq_left rfl, rIM_eq]
  have h := mrep_runG (F := yrM) (FI := yrIM) (R0 := initYG) (prog := genProg)
    (by rw [size_initYG, genProg_length]; exact genProg_idx) hFI h0
    (fun r h1 h2 => by
      rw [size_initYG] at h1 h2 ⊢
      rw [genProg_length] at h2
      exact autRegsB r h1 h2)
  intro r hr
  exact h r (by rw [size_initYG, genProg_length]; omega)

theorem gM_mem_closureY (k : Fin 8) :
    gM k ∈ Subgroup.closure (Set.range fun i : Fin 9 => eM (yRegs.getD i.val 0)) := by
  have hinit : ∀ k, initYG.getD k 1 ∈
      Subgroup.closure (Set.range fun i : Fin 9 => eM (yRegs.getD i.val 0)) := by
    intro k
    by_cases hk : k < 9
    · rw [initYG_getD hk]
      exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩
    · rw [initYG_getD_of_ge (by omega)]
      exact Subgroup.one_mem _
  have h := (allN_iff 8 _).1 chkGenMB k k.isLt
  rw [nthN_eq] at h
  have he := mrep_eq (mrep_genProg _ (genTargets_lt k k.isLt)).1 (chkGensM_spec gensB k).1.1 h
  rw [← he]
  exact runG_mem genProg initYG hinit _

theorem mrep_t4 :
    MRep (powM (wordNM [0, 1, 1]) 3)
      (([0, 1, 1].map fun k => eM (if k = 0 then rN1 else rN2)).prod ^ 3) :=
  mrep_powM (mrep_wordNM regOKK _) 3

theorem t4_factsK :
    let t := ([0, 1, 1].map fun k => eM (if k = 0 then rN1 else rN2)).prod ^ 3
    t * eM (rX.getD 0 0) = eM (rX.getD 0 0) * t ∧ t ^ 4 = 1 ∧ MapsB t [3, 4, 5, 2, 1, 0] := by
  intro t
  have h := chkT4MB
  rw [chkT4M, strictB_eq, chkT4M.t4B, bAnd_eq, bAnd_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx := (mrep_x regOKK 0).1
  have h4 : t ^ 4 = 1 := mrep_eq (mrep_powM mrep_t4 4) mrep_idM h2
  have hinv : MRep (powM (powM (wordNM [0, 1, 1]) 3) 3) t⁻¹ := by
    have e : t ^ 3 = t⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h4)
    rw [← e]
    exact mrep_powM mrep_t4 3
  exact ⟨mrep_eq (mrep_mmul mrep_t4 hx) (mrep_mmul hx mrep_t4) h1, h4,
    mapsBlocksM_spec pivK hinv h3⟩

theorem c_factsK :
    (∀ i < 3, eM (rC.getD i 0) * eM (rX.getD 0 0) = eM (rX.getD 0 0) * eM (rC.getD i 0)) ∧
    eM rK1 = (eM (rC.getD 0 0))⁻¹ * (eM (rC.getD 1 0))⁻¹ * eM (rC.getD 0 0) * eM (rC.getD 1 0) ∧
    eM rK2 = (eM (rC.getD 0 0))⁻¹ * (eM (rC.getD 2 0))⁻¹ * eM (rC.getD 0 0) *
      eM (rC.getD 2 0) := by
  have h := chkCMB
  rw [chkCM, bAnd_eq, bAnd_eq, allL_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hx := (mrep_x regOKK 0).1
  have hr := regOKK
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · have hm : rC.getD i 0 ∈ rC := by
      interval_cases i <;> decide
    have hc : rC.getD i 0 < 200 := by
      interval_cases i <;> decide
    exact mrep_eq (mrep_mmul (hr _ hc).1 hx) (mrep_mmul hx (hr _ hc).1) (h1 _ hm)
  · change eM rK1 = (eM 166)⁻¹ * (eM 167)⁻¹ * eM 166 * eM 167
    have := mrep_eq (hr rK1 (by decide)).1 (mrep_mmul (hr 166 (by decide)).2
      (mrep_mmul (hr 167 (by decide)).2 (mrep_mmul (hr 166 (by decide)).1
        (hr 167 (by decide)).1))) h2
    simp only [mul_assoc] at this ⊢
    exact this
  · change eM rK2 = (eM 166)⁻¹ * (eM 168)⁻¹ * eM 166 * eM 168
    have := mrep_eq (hr rK2 (by decide)).1 (mrep_mmul (hr 166 (by decide)).2
      (mrep_mmul (hr 168 (by decide)).2 (mrep_mmul (hr 166 (by decide)).1
        (hr 168 (by decide)).1))) h3
    simp only [mul_assoc] at this ⊢
    exact this

end CertificateChecks.KernelMisc.ON

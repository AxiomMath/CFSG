module

public import Certificates.Kernel.TcGen.ON
public import Certificates.Data.Inputs2711eON
public import Certificates.Data.Kernel.GenWf
public import Certificates.Data.Kernel.OpsLayT
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.Gen2711.ONTW
public import CFSG.Certificates.Kernel.OpsLayTSound
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.Gen2711.ONTS
meta import Certificates.Data.Inputs2711eON
meta import Certificates.Kernel.Gen2711.ONTW
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e in
meta def CertificateChecks.KernelTc.ON.genProg : List CFSG.SectionRank.Native.Op :=
  onGenProg ++ CFSG.KC.OpsLayK.powOps [(10, 3), (10, 4), (11, 3), (11, 4)] ++ CFSG.KC.OpsLayK.slpW

#lay_snaps CertificateChecks.KernelTc.ON.G 3 154 CertificateChecks.KernelTc.ON.A
  CertificateChecks.KernelTc.ON.B CertificateChecks.KernelTc.ON.genProg 64 32

public section

namespace CertificateChecks.KernelTc.ON

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

@[expose] def powL : List (Nat × Nat) := [(10, 3), (10, 4), (11, 3), (11, 4)]

@[expose] def letL : List (Nat × Nat) :=
  [(8, 1), (9, 1), (10, 1), (11, 1), (10, 3), (10, 4), (11, 3), (11, 4)]

@[expose] def progW : List CFSG.SectionRank.Native.Op :=
  onGenData.prog ++ powOps powL ++ slpW

@[expose] noncomputable def SM : List Nat := G.SL.getD 32 []

@[expose] noncomputable def TM : List Nat := SM.take 27

@[expose] noncomputable def gCh (i : Nat) : Bool :=
  chunkL lay progW 32 i (G.SL.getD i []) (G.SL.getD (i + 1) [])

@[expose] noncomputable def gFa (i : Nat) : Bool :=
  if i = 2 ∨ i = 3 then true else factsL lay TM 27 onGenData.facts 1 i

@[expose] noncomputable def gWA : Bool :=
  wordOK 27 [(0, 1)] && wordOK 27 onGenData.wA && Nat.beq (evalWL lay TM [(0, 1)]) (getR lay SM 27)

@[expose] noncomputable def gWB : Bool :=
  wordOK 27 [(1, 1)] && wordOK 27 onGenData.wB && Nat.beq (evalWL lay TM [(1, 1)]) (getR lay SM 28)

theorem gInit :
    eqL (G.SL.getD 0 []) (initR lay A B 27 ++ List.replicate 37 lay.ONE) = true := by
  quickRfl

theorem gSeeds : seedRegsL lay TM A B 0 1 = true := by quickRfl

theorem gWA_true : gWA = true := by quickRfl

theorem gWB_true : gWB = true := by quickRfl

#kc_each gCh 0 32
#kc_each gFa 0 122

#kc_forall_tree gCh_all (fun i => gCh i = true) 32 CertificateChecks.KernelTc.ON.gCh
#kc_forall_tree gFa_all (fun i => gFa i = true) 122 CertificateChecks.KernelTc.ON.gFa

theorem wA_let : ∀ x ∈ onGenData.wA, x ∈ letL := by
  have h : onGenData.wA.all (fun x => letL.contains x) = true := by decide +kernel
  intro x hx
  simpa using List.all_eq_true.mp h x hx

theorem wB_let : ∀ x ∈ onGenData.wB, x ∈ letL := by
  have h : onGenData.wB.all (fun x => letL.contains x) = true := by decide +kernel
  intro x hx
  simpa using List.all_eq_true.mp h x hx

theorem gCan : letL.all (fun x => CFSG.KC.Ord.validM lay.p (lay.d * lay.S) lay.L lay.H
    (getR lay SM (pReg x.1 x.2))) = true := by
  quickRfl

theorem slp_tgt : ∀ o ∈ slpW, 27 ≤ Op.tgt o ∧ ∀ x ∈ letL, Op.tgt o ≠ pReg x.1 x.2 := by
  decide +kernel

theorem slp_ws : (runWS slpW (initW letL 64)).getD 27 none = some onGenData.wA ∧
    (runWS slpW (initW letL 64)).getD 28 none = some onGenData.wB := by
  decide +kernel

theorem gen271102T_K :
    seedsLT lay A B ⟨onGenData.nregs, onGenData.prog, onGenData.facts⟩ 0 1 = true := by
  have hops : onGenData.prog.all (CFSG.SectionRank.Native.Op.lt 27) = true := by decide +kernel
  have hI : (initR lay A B 27).length = 27 := by simp [initR]
  generalize hR : runF lay onGenData.prog (initR lay A B 27) = R
  have hRl : R.length = 27 := by rw [← hR, runF_length, hI]
  have hPl : (R ++ List.replicate 37 lay.ONE).length = 64 := by simp [hRl]
  obtain ⟨R1, hR1⟩ : ∃ R1, runF lay (powOps powL) (R ++ List.replicate 37 lay.ONE) = R1 := ⟨_, rfl⟩
  have hc : R1 = runF lay [.pow 4 11 32] (runF lay [.pow 3 11 31] (runF lay [.pow 4 10 30]
      (runF lay [.pow 3 10 29] (R ++ List.replicate 37 lay.ONE)))) := by
    rw [← hR1]
    rfl
  have hR1l : R1.length = 64 := by rw [← hR1, runF_length, hPl]
  have hR1ne : ∀ i, (i < 29 ∨ 32 < i) → getR lay R1 i = getR lay (R ++ List.replicate 37 lay.ONE) i := by
    intro i hi
    rw [hc, getR_runF_ne, getR_runF_ne, getR_runF_ne, getR_runF_ne]
    all_goals simp only [Op.tgt]
    all_goals omega
  have hlet : ∀ x ∈ letL, x.1 < 27 ∧ pReg x.1 x.2 ≠ 27 ∧ pReg x.1 x.2 ≠ 28 ∧
      getR lay R1 (pReg x.1 x.2) = powK lay (getR lay R1 x.1) x.2 := by
    intro x hx
    simp only [letL, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, by decide, by decide, rfl⟩
    · exact ⟨by decide, by decide, by decide, rfl⟩
    · exact ⟨by decide, by decide, by decide, rfl⟩
    · exact ⟨by decide, by decide, by decide, rfl⟩
    · refine ⟨by decide, by decide, by decide, ?_⟩
      change getR lay R1 29 = _
      rw [hR1ne 10 (by omega), hc, getR_runF_ne, getR_runF_ne, getR_runF_ne, getR_runF_pow]
      all_goals simp only [Op.tgt, hPl]
      all_goals omega
    · refine ⟨by decide, by decide, by decide, ?_⟩
      change getR lay R1 30 = _
      rw [hR1ne 10 (by omega), hc, getR_runF_ne, getR_runF_ne, getR_runF_pow, getR_runF_ne]
      all_goals simp only [Op.tgt, runF_length, hPl]
      all_goals omega
    · refine ⟨by decide, by decide, by decide, ?_⟩
      change getR lay R1 31 = _
      rw [hR1ne 11 (by omega), hc, getR_runF_ne, getR_runF_pow, getR_runF_ne, getR_runF_ne]
      all_goals simp only [Op.tgt, runF_length, hPl]
      all_goals omega
    · refine ⟨by decide, by decide, by decide, ?_⟩
      change getR lay R1 32 = _
      rw [hR1ne 11 (by omega), hc, getR_runF_pow, getR_runF_ne, getR_runF_ne, getR_runF_ne]
      all_goals simp only [Op.tgt, runF_length, hPl]
      all_goals omega
  have hS : runF lay slpW R1 = SM := by
    have h1 : Snd.runL lay progW (G.SL.getD 0 []) = G.SL.getD 32 [] :=
      runL_of_chunks (c := lay) (prog := progW) (k := 32) (m := 32)
        (S := fun i => G.SL.getD i []) (by decide +kernel) gCh_all
    rw [eq_of_eqL gInit] at h1
    change runF lay progW _ = _ at h1
    unfold progW at h1
    rw [runF_append, runF_append, runF_append_regs lay _ _ hops _ hI, hR, hR1] at h1
    exact h1
  have hlow : ∀ i, i < 27 → getR lay SM i = getR lay R i := fun i hi => by
    rw [← hS, getR_runF_notTgt lay slpW R1 i fun o ho => by have := (slp_tgt o ho).1; omega,
      hR1ne i (by omega), getR_append lay _ (by omega)]
  have hCan : ∀ x ∈ letL, CFSG.KS.Ord.Canon lay.p lay.d lay.w (getR lay R1 (pReg x.1 x.2)) := fun x hx => by
    have e := getR_runF_notTgt lay slpW R1 (pReg x.1 x.2) fun o ho => (slp_tgt o ho).2 x hx
    rw [hS] at e
    rw [← e]
    exact CFSG.KS.Ord.validM_canon (show CFSG.KC.Ord.constsOK lay.p lay.w lay.S lay.d lay.T lay.L lay.H lay.CM lay.RM
      lay.ONE lay.LV lay.HV = true from lay_ok) (List.all_eq_true.mp gCan x hx)
  have hW0 : WInv lay R1 R1 (initW letL 64) := by
    refine ⟨by rw [hR1l]; rfl, fun i u hu => ?_⟩
    obtain ⟨⟨r, e⟩, hx, rfl, rfl⟩ := getD_initW letL 64 i u hu
    have hL := hlet (r, e) hx
    have hP : CFSG.KS.Ord.Canon lay.p lay.d lay.w (powK lay (getR lay R1 r) e) := by
      have h := hCan (r, e) hx
      rw [hL.2.2.2] at h
      exact h
    refine ⟨fun y hy => by rw [List.mem_singleton.mp hy]; exact hP, ?_⟩
    rw [evalWL, evalWL, lay_mul_one lay lay_ok hP]
    exact hL.2.2.2
  have hWS := runF_runWS lay lay_ok R1 slpW R1 (initW letL 64) hW0
  rw [hS] at hWS
  have hfun : ∀ i, getR lay R i = getR lay TM i := by
    intro i
    by_cases hi : i < 27
    · rw [TM, getR_take lay SM hi, hlow i hi]
    · rw [getR_of_le lay (by omega), getR_of_le lay (by rw [TM, List.length_take]; omega)]
  have hR1T : ∀ x ∈ letL, getR lay TM x.1 = getR lay R1 x.1 := fun x hx => by
    have h27 := (hlet x hx).1
    rw [hR1ne _ (by omega), getR_append lay _ (by omega), hfun]
  have hwA : evalWL lay TM onGenData.wA = getR lay SM 27 := by
    rw [(hWS.2 27 _ slp_ws.1).2]
    exact evalWL_congrW lay onGenData.wA fun x hx => hR1T x (wA_let x hx)
  have hwB : evalWL lay TM onGenData.wB = getR lay SM 28 := by
    rw [(hWS.2 28 _ slp_ws.2).2]
    exact evalWL_congrW lay onGenData.wB fun x hx => hR1T x (wB_let x hx)
  have hfa : onGenData.facts.all (factL lay TM 27) = true := by
    refine all_of_chunks (k := 1) (m := 122) (by decide +kernel) fun i hi => ?_
    by_cases h2 : i = 2
    · subst h2
      have e : (onGenData.facts.drop (2 * 1)).take 1 = [.eq [(0, 1)] onGenData.wA] := rfl
      change ((onGenData.facts.drop (2 * 1)).take 1).all (factL lay TM 27) = true
      rw [e, List.all_cons, List.all_nil, Bool.and_true]
      exact factL_eq_of lay hwA gWA_true
    by_cases h3 : i = 3
    · subst h3
      have e : (onGenData.facts.drop (3 * 1)).take 1 = [.eq [(1, 1)] onGenData.wB] := rfl
      change ((onGenData.facts.drop (3 * 1)).take 1).all (factL lay TM 27) = true
      rw [e, List.all_cons, List.all_nil, Bool.and_true]
      exact factL_eq_of lay hwB gWB_true
    have h := gFa_all i hi
    rw [gFa, ite_eq_right (by omega)] at h
    exact h
  have hfl : factL lay R 27 = factL lay TM 27 := funext (factL_congrW lay hfun 27)
  have he := gSeeds
  simp only [seedRegsL, Bool.and_eq_true] at he
  rw [seedsLT_eq]
  unfold seedsL
  rw [Snd.runC_eq]
  change (progOK 27 onGenData.prog && decide (0 < 27) && decide (1 < 27) &&
    (onGenData.facts.all (factL lay (runF lay onGenData.prog (initR lay A B 27)) 27) &&
      Nat.beq (getR lay (runF lay onGenData.prog (initR lay A B 27)) 0) A &&
      Nat.beq (getR lay (runF lay onGenData.prog (initR lay A B 27)) 1) B)) = true
  rw [hR, hfl, hfa, hfun 0, hfun 1, he.1, he.2]
  have hprog : progOK 27 onGenData.prog = true := by decide +kernel
  rw [hprog]
  rfl

theorem gen271102T_D : genWf 3 onGenData = true := by
  decide +kernel

theorem chW_neg : (!chunkL lay progW 32 0 (G.SL.getD 0 []) (G.SL.getD 2 [])) = true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay TM B A 0 1) = true := by
  quickRfl

end CertificateChecks.KernelTc.ON

end

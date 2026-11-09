module

public import Certificates.Kernel.McertP.LyRun
public import Certificates.Data.Kernel.AlphaGrpK
import CFSG.Certificates.Kernel.AlphaGrpKSound

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelMP.Ly

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaLy

theorem ly31_wf : ly_31_claims.wf = true := by decide +kernel

theorem ly7_wf : ly_7_claims.wf = true := by decide +kernel

theorem alpha_restA : (lyMod.wf 3 && pcWf (lyTops ++ lyMod.basisPc 3) &&
    lyTops.all (fun q => lyMod.acts.any (·.reg == q.reg))) = true := by
  decide +kernel

theorem alpha_wTops : lyTidx.all (fun i => decide (i < lyMod.acts.length) &&
    lyTops.any (·.reg == (lyMod.acts.getD i default).reg)) = true := by
  decide +kernel

theorem alpha_wNodup : ((wordsL 3 lyMod.basis.length
    (lyTidx.map fun i => (lyMod.acts.getD i default).mat)).map (codeL 3)).Nodup := by
  decide +kernel

theorem alpha_wCount : decide (3 ^ 7 ≤ (wordsL 3 lyMod.basis.length
    (lyTidx.map fun i => (lyMod.acts.getD i default).mat)).length * 3 ^ lyMod.basis.length) =
    true := by
  decide +kernel

def lanes2 (T : Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => (T &&& 3) :: lanes2 (T >>> 2) n

theorem lanes2_getD (T : Nat) : ∀ (n i : Nat),
    (lanes2 T n).getD i 0 = if i < n then (T >>> (2 * i)) &&& 3 else 0
  | 0, i => by simp [lanes2]
  | n + 1, 0 => by simp [lanes2]
  | n + 1, i + 1 => by
    rw [lanes2, List.getD_cons_succ, lanes2_getD (T >>> 2) n i]
    have e : 2 * (i + 1) = 2 + 2 * i := by omega
    rw [e, Nat.shiftRight_add]
    by_cases h : i < n <;> simp [h]

def lyCfPk : Nat := 5995079717730634106267594045087399410748489048526850

def lyCfK (r₀ j s : Nat) : Int :=
  if (r₀ * 4 + j) * 5 + s < 100 then
    ((lyCfPk >>> (2 * ((r₀ * 4 + j) * 5 + s)) &&& 3 : Nat) : Int)
  else 0

theorem lyCfArr_toList : lyCfArr.toList = lanes2 lyCfPk 100 := by decide +kernel

theorem lyCf_eq : lyCf = lyCfK := by
  funext r j s
  rw [lyCf, lyCfK, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, lyCfArr_toList,
    ← List.getD_eq_getElem?_getD, lanes2_getD]
  split_ifs <;> rfl

set_option maxHeartbeats 0 in
theorem alpha_fun : lyMod.funOK 3 lyCf = true := by
  rw [lyCf_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem alpha_altW : altW 3 lyMod 5 4 2500 625 lyCiSp [] tgtAlt = true := by decide +kernel

theorem alpha_alt : lyMod.altOK 3 lyCi lyCt tgtAlt = true := by
  have hct : ∀ a b r s, lyCt a b r s =
      (((([] : List (Nat × Nat)).foldl (fun arr x => arr.set! x.1 x.2)
        (Array.replicate 625 0)).getD (((a * 5 + b) * 5 + r) * 5 + s) 0 : Nat) : Int) := by
    intro a b r s
    simp only [lyCt, List.foldl_nil, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  exact altOK_of_altW (fun _ _ _ _ _ => rfl) hct alpha_altW

theorem alpha_len : decide (3 ≤ lyMod.basis.length) = true := by decide +kernel

theorem alpha_restB : (decide (3 ≤ lyMod.basis.length) && lyMod.funOK 3 lyCf &&
    lyMod.altOK 3 lyCi lyCt tgtAlt) = true := by
  rw [alpha_len, alpha_fun, alpha_alt]
  rfl

theorem ly31_neg : (!mcertL lay B A ⟨2, [], ly_31_claims.baseFacts⟩) = true := by decide +kernel

theorem ly7_neg :
    (!chunkL lay ly_7_claims.prog 100 0 (initR lay B A ly_7_claims.nregs) (W7.SL.getD 1 [])) =
      true := by
  decide +kernel

theorem alpha_neg : (!chunkL lay lyProg 100 0 (initR lay B A lyNregs) (WA.SL.getD 1 [])) = true := by
  decide +kernel

end CertificateChecks.KernelMP.Ly

end

module

public import Certificates.Kernel.McertP.HNRun

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelMP.HN

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaHN CFSG.SectionRank.Native
  CFSG.RankThree.Asc83Table.Native

theorem hn7_wf : hn_7_claims.wf = true := by decide +kernel

theorem alpha_restA : (hnMod.wf 3 && pcWf (hnTops ++ hnMod.basisPc 3) &&
    hnMod.acts.all (fun g => g.mat.all (· < 3)) &&
    hnTops.all (fun q => hnMod.acts.any (·.reg == q.reg))) = true := by
  decide +kernel

theorem alpha_grp : hnMod.grpOK hnTops hnGs = true := by decide +kernel

theorem alpha_rank : decide (3 ≤ hnMod.basis.length) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem alpha_fun : hnMod.funOK 3 hnCf = true := by decide +kernel

def hnCiPk : Nat :=
  245616231268539211200726777212793595161718640746464177589024166381774167696155813542656204843212547492915599758503651985471312042084135167284848378918842353235507355279818954297502491737327824394522594456124669680571224949941413624424909461928563046516399534864665523069752104519411222679675758582065485977722346858485301083349876769515893963531763898614830474245811103744784602577680258321039192837250718750241702712123399571346624263513653506857598661601186820215895044809363148756660155790005411914557251230987607614954278683762364473012372433366599083156128105608414568559169118444840276174112289448271774872575935960389780549688217229739524720641283979574095201753793752990527269311163485044860602804466388776416602024612765968831949072639617344668463960228327939844585315122430659063766911486615153647395462114857725457139496925145477647903941498430822479343400495092773162138287820402576919762266861562252182292130798621712846355237319356933382115477230054046585641478133742035841515272178170118094790773769077076427237208524892762511824275598237654639694220117903666430540156268879299408640170720018342992565098617152499056207048651196324561029729521971126420017766588381900984537006354618331994215528096104370632794550645937436500672451104532344415348738194172952610750531034194604614598424283669323693110579508715701340964044608892455713451105994667869280359912260693026544910004287709196500261316327807279682411939179867790350858073687677770945379066013834685094646030362827115422495124289822513938515136669212814358500545842247998540655354282222918742314250665988

def hnCiK (a₀ b₀ j r s : Nat) : Int :=
  if (((a₀ * 4 + b₀) * 11 + j) * 4 + r) * 4 + s < 2816 then
    ((hnCiPk >>> (2 * ((((a₀ * 4 + b₀) * 11 + j) * 4 + r) * 4 + s)) &&& 3 : Nat) : Int)
  else 0

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

theorem hnCiArr_toList : hnCiArr.toList = lanes2 hnCiPk 2816 := by decide +kernel

theorem hnCi_eq : hnCi = hnCiK := by
  funext a b j r s
  rw [hnCi, hnCiK, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hnCiArr_toList,
    ← List.getD_eq_getElem?_getD, lanes2_getD]
  split_ifs <;> rfl

set_option maxHeartbeats 0 in
theorem alpha_alt : hnMod.altOK 3 hnCi hnCt tgtAlt = true := by
  rw [hnCi_eq]
  decide +kernel

end CertificateChecks.KernelMP.HN

end

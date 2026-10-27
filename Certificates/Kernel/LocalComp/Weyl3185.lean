module

public import Certificates.Kernel.LocalComp.E8Tables
public import Certificates.Kernel.LocalComp.Omega1Chain
public import Certificates.Kernel.OmegaEight.Aut
public import CFSG.Certificates.Kernel.O8ConstrSound
public import CFSG.Certificates.Kernel.LocalCompBridgeSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.LocalCompAglSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylBridgeData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.LocalCompFrameSound
public import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3185

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KLC.E8 CFSG.EvenSmallLie
  CFSG.EvenSmallLie.OmegaEight.Weyl CertificateChecks.KernelLC CertificateChecks.KernelO8

@[expose] noncomputable def PAP : Nat := nat_lit 21246585917042041646735096408028924245974135134032433796560017461136920273445573091270960654252176674904866167891238226512259111164253726463487791793769779925109966999484115015540447999026762997490784778426018709317224446262726854259043307088724657335082754401190914508943162736962760278173025257565768205813505381335935667487253767947801190729285679252302318856323532397031252422064467263826000714393909159144752557214517710720256010249843164010087520379573368190395464797037877812118932310014042510603998456710770354423288637906670691847115769230128466496798574971589688363265

@[expose] noncomputable def PRP : Nat := nat_lit 4363511855640283874378821670814145238966805346533018482101949240357371211120565008479264730587446750916759474817074020826279694780975464822718909861175750699566895405205174872763711043973242757446952482638514658186165385646707756813196630531473987528372499126169734553155658994363835416751

@[expose] noncomputable def FRP : Nat := nat_lit 7812998068708900865

@[expose] noncomputable def OWP : Nat :=
  nat_lit 62709831082250008409159317249141594435997582699704744813442561472827502734437

theorem kPA : bindList pairArr.toList 240 PAP = true := by quickRfl
theorem kPR : bindList pairRepArr.toList 120 PRP = true := by quickRfl
theorem kF : bindList frameRootList 8 FRP = true := by quickRfl
theorem kOW : allN 8 (fun i => bindList (omWords.getD i []) 4 (owK OWP i)) = true := by quickRfl
theorem kP : pairK E8.NEG PAP PRP = true := by quickRfl
theorem kZ : zK E8.RT E8.NEG FRP = true := by quickRfl
theorem kO : omK E8.RT PAP PRP OWP Om1.S = true := by quickRfl
theorem kT : triK E8.RT E8.NEG OWP = true := by quickRfl
theorem kS0 : notB' (siftK 120 9 (mask 9) (120 * 9) (pidn 120 9) Om1.LR Om1.TRI Om1.BP 7 0
    (pairImg E8.RT PAP PRP 1)) = true := by
  quickRfl

theorem perm1 : allN 17 (fun j => permOK 120 9 (mask 9) (120 * 9) (Om1.S j) (Om1.SI j)) = true := by
  quickRfl

theorem kGen1 : allN 8 (fun j => strictB (genP NSP NIP j) fun g => allN 120 fun i =>
    Nat.beq (pg 9 511 (Om1.S j) i) (pg 9 511 g i)) = true := by
  quickRfl

theorem genArrs_eq :
    OmegaEight.genArrs = genArrsPG OmegaEight.qNat OmegaEight.bNat OmegaEight.rootPairs := rfl

theorem copy0_gen {j : Nat} (hj : j < 8) :
    OmegaEight.copy0Arr OmegaEight.genArrs[j]! = unpack 120 9 (Om1.S j) := by
  obtain ⟨hs, he⟩ := genP_sound formP kNsP rootPairs_bind
  rw [genArrs_eq, he j (by omega)]
  apply Array.ext
  · simp [OmegaEight.copy0Arr, unpack]
  · intro i h1 h2
    have hi : i < 120 := by simpa [OmegaEight.copy0Arr] using h1
    simp only [OmegaEight.copy0Arr, unpack, Array.getElem_ofFn]
    rw [getElem!_pos _ i (by simp; omega), Array.getElem_ofFn]
    have hj' := allN_spec kGen1 j hj
    rw [strictB_eq'] at hj'
    exact (Nat.eq_of_beq_eq_true (allN_spec hj' i hi)).symm

theorem genOm1 : ((OmegaEight.genArrs.extract 0 8).map OmegaEight.copy0Arr).size = 8 ∧
    ∀ j < 8, ((OmegaEight.genArrs.extract 0 8).map OmegaEight.copy0Arr)[j]! =
      unpack 120 9 (Om1.S j) := by
  obtain ⟨hs, -⟩ := genP_sound formP kNsP rootPairs_bind
  rw [← genArrs_eq] at hs
  refine ⟨by simp [hs], fun j hj => ?_⟩
  rw [getElem!_pos _ j (by simp [hs]; omega), ← copy0_gen hj, getElem!_pos _ j (by omega)]
  simp

theorem binds1 : Binds 120 9 Om1.S 17 7 Om1.BP OmegaEight.omega1S
    ((OmegaEight.omega1Base.map Fin.val).toArray) := by
  obtain ⟨hs, he⟩ := pushWords_eq genOm1 Om1.head
  refine ⟨by decide, by decide, by decide, hs, he, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3185 : (pairCheck = true)
    ∧ (zWordCheck = true)
    ∧ (omCheck = true)
    ∧ (sZeroCheck = true)
    ∧ (trialityCheck = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [pairCheck_eq]
    exact pair_sound E8.bind E8.sorted E8.hrt E8.neg kPA kPR kP
  · rw [zWordCheck_eq]
    exact zWord_sound E8.bind E8.sorted E8.hrt E8.neg kF kZ
  · rw [omCheck_eq]
    exact om_sound E8.bind E8.sorted E8.hrt E8.neg kPA kPR kOW (fun j hj => copy0_gen hj) kO
  · rw [sZeroCheck_eq]
    exact sZero_sound E8.bind E8.sorted E8.hrt E8.neg kPA kPR kP binds1 perm1 Om1.hl kS0
  · rw [trialityCheck_eq]
    exact triality_sound E8.bind E8.sorted E8.hrt E8.neg kOW kT

end CertificateChecks.KernelLC.W3185

end

module

public import Certificates.Kernel.Sporadic.ONLine.Ln0
public import Certificates.Kernel.Sporadic.ONLine.Ln1
public import Certificates.Kernel.Sporadic.ONLine.Ln2
public import Certificates.Kernel.Sporadic.ONLine.Ln3
public import Certificates.Kernel.Sporadic.ONLine.Ln4
public import Certificates.Kernel.Sporadic.ONLine.Ln5
public import Certificates.Kernel.Sporadic.ONLine.Ln6
public import Certificates.Kernel.Sporadic.ONLine.Ln7
public import Certificates.Kernel.Sporadic.ONLine.Ord
public import Certificates.Kernel.Sporadic.ONLine.Pi0
public import Certificates.Kernel.Sporadic.ONLine.Pi1
public import Certificates.Kernel.Sporadic.ONLine.Pi2
public import Certificates.Kernel.Sporadic.ONLine.Pi3
public import Certificates.Kernel.Sporadic.ONLine.Pre
public import Certificates.Kernel.Sporadic.ON.Minus2124
public import Certificates.Kernel.Sporadic.ON.Final
public import CFSG.Certificates.Kernel.Spor.ONLineSound
public import CFSG.Certificates.Kernel.Spor.ONDiscSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.Spor.ONMvSound

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.ONLine.lnAll CertificateChecks.KernelSpor.ONLine.lnS 1023

#kon_join CertificateChecks.KernelSpor.ONLine.lordAll CertificateChecks.KernelSpor.ONLine.lordS 1023

#kon_join CertificateChecks.KernelSpor.ONLine.lsortAll CertificateChecks.KernelSpor.ONLine.lsortS 1023

#kon_join CertificateChecks.KernelSpor.ONLine.piAll CertificateChecks.KernelSpor.ONLine.piS 1023

#kon_join CertificateChecks.KernelSpor.ONLine.preAll CertificateChecks.KernelSpor.ONLine.preS 1023

namespace CertificateChecks.KernelSpor.ONLine

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONLine CFSG.F3.Native CFSG.Sporadic.Fi23.Native
open CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native

theorem nx0 : Nat.beq (ONL.NX 0) 1 = true := by quickRfl
theorem nx1 : Nat.beq (ONL.NX 1023) 122760 = true := by quickRfl
theorem pi0 : Nat.beq (tab ONL.PI 0) 0 = true := by quickRfl

theorem ln_pt : ∀ h < 122760, lineAt ONL.K ONL.LP ONV.LA ONV.LB ONL.A ONL.B 122760 h = true :=
  fun h hh => slice_pt (F := lineAt ONL.K ONL.LP ONV.LA ONV.LB ONL.A ONL.B 122760) (SL := 120)
    (NS := 1023) lnAll h (by omega)

theorem sort_pt : ∀ i < 122760, sortAt ONL.K ONL.SO ONL.SOI 122760 i = true :=
  fun i hi => slice_pt (F := sortAt ONL.K ONL.SO ONL.SOI 122760) (SL := 120) (NS := 1023)
    lsortAll i (by omega)

theorem pi_pt : ∀ i < 245520,
    piAt ONV.K ONN.NEG ONV.A ONV.B ONL.K ONL.A ONL.B ONL.PI 122760 i = true :=
  fun i hi => slice_pt (F := piAt ONV.K ONN.NEG ONV.A ONV.B ONL.K ONL.A ONL.B ONL.PI 122760)
    (SL := 240) (NS := 1023) piAll i (by omega)

theorem pre_pt : ∀ j < 122760, preAt ONL.PI ONL.PRE 245520 j = true :=
  fun j hj => slice_pt (F := preAt ONL.PI ONL.PRE 245520) (SL := 120) (NS := 1023) preAll j
    (by omega)

theorem colsA_eq : colsA.size = 154 ∧ ONV.LA.length = 154 ∧
    ∀ j < 154, colsA[j]! = wOfK (ONV.LA.getD j 0) := by
  unfold colsA rowsA
  exact ON.cols_of ONSeedA.eq ON.colsAK (ON.list_eq ONV.LA ONV.CA (allN_spec ON.listA)) rfl

theorem colsB_eq : colsB.size = 154 ∧ ONV.LB.length = 154 ∧
    ∀ j < 154, colsB[j]! = wOfK (ONV.LB.getD j 0) := by
  unfold colsB rowsB
  exact ON.cols_of ONSeedB.eq ON.colsBK (ON.list_eq ONV.LB ONV.CB (allN_spec ON.listB)) rfl

theorem colsA_canon : ∀ j < 154, canon (ONV.LA.getD j 0) = true :=
  ON.canon_of ON.colsAK (ON.list_eq ONV.LA ONV.CA (allN_spec ON.listA))

theorem colsB_canon : ∀ j < 154, canon (ONV.LB.getD j 0) = true :=
  ON.canon_of ON.colsBK (ON.list_eq ONV.LB ONV.CB (allN_spec ON.listB))

theorem root_eq : digitsW CFSG.ONSchreier.Data.rootDigits = wOfK (key ONV.K 0) := by
  rw [ONRoot.eq, digitsK_sound ON.rootK]

theorem nu_vec {i : Nat} (hi : i < 245520) :
    nuW (wOfK (key ONV.K i)) = wOfK (key ONL.K (tab ONL.PI i)) := by
  obtain ⟨p1, pm, -⟩ := piAt_spec (pi_pt i hi)
  obtain ⟨c, l, -⟩ := lineAt_spec (ln_pt _ p1)
  exact nuW_of_lead1 c l (pmEq_spec pm)

theorem root_line : nuW (digitsW CFSG.ONSchreier.Data.rootDigits) = wOfK (key ONL.K 0) := by
  rw [root_eq, nu_vec (by norm_num), Nat.eq_of_beq_eq_true pi0]

theorem line_eq :
    (lineBFS colsA colsB (digitsW CFSG.ONSchreier.Data.rootDigits) 122760).keys =
        (Array.ofFn (n := 122760) fun i => wOfK (key ONL.K i.val)) ∧
      natTab (lineBFS colsA colsB (digitsW CFSG.ONSchreier.Data.rootDigits) 122760).alpha =
        (Array.ofFn (n := 122760) fun i => tab ONL.A i.val) ∧
      natTab (lineBFS colsA colsB (digitsW CFSG.ONSchreier.Data.rootDigits) 122760).beta =
        (Array.ofFn (n := 122760) fun i => tab ONL.B i.val) :=
  line_sim (SL := 120) (NS := 1023) colsA_eq colsB_eq colsA_canon colsB_canon root_line
    (by norm_num) ln_pt (by norm_num) (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1)
    lordAll sort_pt

theorem key_neg {i : Nat} (hi : i < 245520) : key ONV.K (tab ONN.NEG i) = vneg (key ONV.K i) := by
  have e := ON.pt_of ON.negAll (fun _ => rfl) i hi
  unfold negAt at e
  rw [ON.strictB_eq'] at e
  obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 e
  exact Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 h2).1

theorem line_cert_ok : lineCert (digitsW CFSG.ONSchreier.Data.rootDigits) 122760 3 = true := by
  obtain ⟨hU, hUa, hUb⟩ := line_eq
  have hO := ON.keys_eq
  obtain ⟨hOa, hOb⟩ := ON.orb_tabs ON.mvAll ON.ordAll ON.sortAll
  unfold tabArr at hOa hOb
  have hsig := ON.sigma_eq
  unfold CFSG.Sporadic.ONOddCore.sigmaArr at hsig
  unfold lineCert
  dsimp only
  generalize lineBFS colsA colsB (digitsW CFSG.ONSchreier.Data.rootDigits) 122760 = U at hU hUa hUb ⊢
  generalize vorbit (digitsW CFSG.ONSchreier.Data.rootDigits) = O at hO hOa hOb hsig ⊢
  have hkU : ∀ j < 122760, U.keys[j]! = wOfK (key ONL.K j) := fun j hj => by
    rw [hU, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have hkO : ∀ i < 245520, O.keys[i]! = wOfK (key ONV.K i) := fun i hi => by
    rw [hO, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  have hcL : ∀ j < 122760, canon (key ONL.K j) = true := fun j hj => (lineAt_spec (ln_pt j hj)).1
  have hposU : ∀ j < 122760, posOf (indexOf U.keys) 122760 (wOfK (key ONL.K j)) = j :=
    fun j hj => by
      rw [← hkU j hj]
      exact index_sound hU hcL sort_pt j hj 122760
  have hpi : piTab O (posOf (indexOf U.keys) 122760) =
      Array.ofFn (n := 245520) fun i => tab ONL.PI i.val := by
    apply Array.ext
    · simp [piTab]
    · intro i h1 h2
      have hi : i < 245520 := by simpa using h2
      simp only [piTab, Array.getElem_ofFn]
      rw [hkO i hi, nu_vec hi, hposU _ (piAt_spec (pi_pt i hi)).1]
  rw [hpi, hsig]
  have hmv := fun i (hi : i < 245520) => mvAt_spec (ON.pt_of ON.mvAll (fun _ => rfl) i hi)
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold linesOK
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨⟨by rw [hU, Array.size_ofFn], size_of_natTab hUa⟩, size_of_natTab hUb⟩, ?_⟩, ?_⟩,
      ?_⟩
    · apply parAll_of
      intro j hj
      obtain ⟨c, l, a1, b1, -, -⟩ := lineAt_spec (ln_pt j hj)
      obtain ⟨⟨ia, -⟩, ⟨ib, -⟩⟩ := line_img colsA_eq colsB_eq colsA_canon colsB_canon ln_pt hj
      simp [lineCheckAt, hkU j hj, ap_of hUa hj, ap_of hUb hj, hkU _ a1, hkU _ b1, a1, b1,
        canon_sound c, hposU j hj, nuW_of_lead1 c l (Or.inl rfl), wOfK_ne_zero c l, ia, ib]
    · apply allIn0_of
      intro i hi
      obtain ⟨p1, -, pneg, nne, pa, pb⟩ := piAt_spec (pi_pt i hi)
      obtain ⟨n1, n2⟩ := ON.neg_facts hi
      obtain ⟨-, ma, mb, -, -⟩ := hmv i hi
      simp [ofFnGet hi, ofFnGet n1, ofFnGet ma, ofFnGet mb, hkU _ p1, hkO i hi, hkO _ n1,
        nu_vec hi, key_neg hi, ← wOfK_vneg (ON.canon_key i hi), ap_of hOa hi, ap_of hOb hi,
        ap_of hUa p1, ap_of hUb p1, p1, n1, n2, nne, pneg, pa, pb]
    · apply allIn0_of
      intro j hj
      have hlt : ∀ i < nPts, (Array.ofFn (n := 245520) fun i => tab ONL.PI i.val)[i]! < 122760 :=
        fun i hi => by
          rw [ofFnGet hi]
          exact (piAt_spec (pi_pt i hi)).1
      have hsurj : ∀ j < 122760, ∃ i < nPts,
          (Array.ofFn (n := 245520) fun i => tab ONL.PI i.val)[i]! = j := fun j hj => by
        obtain ⟨h1, h2⟩ := preAt_spec (pre_pt j hj)
        exact ⟨_, h1, by rw [ofFnGet h1, h2]⟩
      obtain ⟨h1, h2⟩ := piPre_spec hlt hsurj j hj
      rw [ofFnGet h1] at h2
      simp [h1, h2]
  · rw [hkU 0 (by norm_num), root_line]
  · apply discOK_of_hits
    intro k hk1 hk2
    obtain ⟨q, hq, h⟩ := hits_of_ordRun (SL := 120) (NS := 1023) (by norm_num) (by norm_num)
      (Nat.eq_of_beq_eq_true nx0) (Nat.eq_of_beq_eq_true nx1) lordAll k hk1 hk2
    exact ⟨q, hq, by rw [ap_of hUa (by omega), ap_of hUb (by omega)]; exact h⟩

end CertificateChecks.KernelSpor.ONLine

end

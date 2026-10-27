module

public import Certificates.Kernel.Sporadic.ON3.Small
public import Certificates.Kernel.Sporadic.ON3.Data2
public import CFSG.Certificates.Kernel.Spor.ChainFKSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.ChainKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.KC.Enum CFSG.KS CFSG.KS.CB CFSG.KS.CH CFSG.KS.PW CFSG.ONSchreier CFSG.ONSchreier.Native

@[expose] noncomputable def uI (y : Nat) : Nat := CFSG.KS.ON.tab ON3P.UI y

@[expose] noncomputable def pF (j x : Nat) : Nat := CFSG.KS.ON.tab ON3P.FW (Nat.add (Nat.mul 120 j) x)

@[expose] noncomputable def pFI (j x : Nat) : Nat :=
  CFSG.KS.ON.tab ON3P.INV (Nat.add (Nat.mul 120 j) x)

@[expose] noncomputable def pPTS : Nat → Nat → Nat := lv3 ON3LP.PTS0 ON3LP.PTS1 ON3LP.PTS2
@[expose] noncomputable def pPOS : Nat → Nat → Nat := lv3 ON3LP.POS0 ON3LP.POS1 ON3LP.POS2
@[expose] noncomputable def pPAR : Nat → Nat → Nat := lv3 ON3LP.PAR0 ON3LP.PAR1 ON3LP.PAR2
@[expose] noncomputable def pLAB : Nat → Nat → Nat := lv3 ON3LP.LAB0 ON3LP.LAB1 ON3LP.LAB2
@[expose] noncomputable def pMr : Nat → Nat := nat3 ON3LP.M0 ON3LP.M1 ON3LP.M2
@[expose] noncomputable def pIDX (i t : Nat) : Nat :=
  nIf(Nat.beq i 0, t, nIf(Nat.beq i 1, Nat.mul 2 t, Nat.add 4 (Nat.mul 2 t)))
@[expose] noncomputable def pLEN : Nat → Nat := nat3 12 6 3
@[expose] noncomputable def pB : Nat → Nat := fun k => nat3 0 3 1 k

@[expose] noncomputable def uG (j x : Nat) : Nat :=
  Data.quotientConjugator[(bL[j]!)[uI x]!]!

@[expose] noncomputable def pslOK : Bool :=
  bAnd(allN 12 (fun j => allN 120 fun x => bAnd(Nat.beq ((Data.PSL120Chain.strongGenerators[j]!)[x]!)
      (pF j x), bAnd(Nat.blt (pF j x) 120,
      bAnd(Nat.blt (pFI j x) 120, Nat.beq (pFI j (pF j x)) x)))),
  bAnd(allN 120 (fun x => bAnd(Nat.blt Data.quotientConjugator[x]! 120,
      Nat.beq (uI Data.quotientConjugator[x]!) x)),
  bAnd(allN 3 (fun i => bAnd(idxOK pF 12 pB i (pIDX i) (pLEN i),
      bAnd(cbHead 120 (pMr i) (pB i) (pPTS i) (pPAR i) (pLAB i),
      bAnd(allN (pMr i) (cbPt 120 (pMr i) (Nat.mul 2 (pLEN i)) (stepX pF pFI (pIDX i) (pLEN i))
          (pPTS i) (pPOS i) (pPAR i) (pLAB i)),
        allN 120 (cbPos 120 (pMr i) (pPTS i) (pPOS i)))))),
    allN 2 fun j => siftFull3 120 pPOS pPAR pLAB pMr (fun i => invX pF pFI (pIDX i) (pLEN i)) pB
      (uG j))))

theorem psl_ok : pslOK = true := by quickRfl

theorem psl_parts : (∀ j < 12, ∀ x < 120, (Data.PSL120Chain.strongGenerators[j]!)[x]! = pF j x ∧
      pF j x < 120 ∧ pFI j x < 120 ∧ pFI j (pF j x) = x) ∧
    (∀ x < 120, Data.quotientConjugator[x]! < 120 ∧ uI Data.quotientConjugator[x]! = x) ∧
    (∀ i < 3, idxOK pF 12 pB i (pIDX i) (pLEN i) = true ∧
      cbHead 120 (pMr i) (pB i) (pPTS i) (pPAR i) (pLAB i) = true ∧
      (∀ k < pMr i, cbPt 120 (pMr i) (Nat.mul 2 (pLEN i)) (stepX pF pFI (pIDX i) (pLEN i))
          (pPTS i) (pPOS i) (pPAR i) (pLAB i) k = true) ∧
      ∀ z < 120, cbPos 120 (pMr i) (pPTS i) (pPOS i) z = true) ∧
    ∀ j < 2, siftFull3 120 pPOS pPAR pLAB pMr (fun i => invX pF pFI (pIDX i) (pLEN i)) pB
      (uG j) = true := by
  have h := psl_ok
  unfold pslOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun j hj x hx => ?_, fun x hx => ?_, fun i hi => ?_, fun j hj => allN_spec h4 j hj⟩
  · have := allN_spec (allN_spec h1 j hj) x hx
    simp only [bAnd_iff, Nat.beq_eq] at this
    exact ⟨this.1, by simpa using this.2.1, by simpa using this.2.2.1, this.2.2.2⟩
  · have := allN_spec h2 x hx
    simp only [bAnd_iff, Nat.beq_eq] at this
    exact ⟨by simpa using this.1, this.2⟩
  · have := allN_spec h3 i hi
    simp only [bAnd_iff] at this
    exact ⟨this.1, this.2.1, allN_spec this.2.2.1, allN_spec this.2.2.2⟩

theorem uinv_get {y : Nat} (hy : y < 120) :
    (pinvCand 120 Data.quotientConjugator)[y]! = uI y := by
  have hs : Data.quotientConjugator.size = 120 := rfl
  rw [arr_ext (F := fun x => Data.quotientConjugator[x]!) hs fun _ _ => rfl]
  exact CFSG.KS.CB.pinvCand_get (fun x hx => (psl_parts.2.1 x hx).1)
    (fun x hx => (psl_parts.2.1 x hx).2) hy

theorem u_facts : pisInv 120 Data.quotientConjugator (pinvCand 120 Data.quotientConjugator) = true ∧
    allBelowN 2 (fun j => memFull 120
      (cLevels 120 Data.PSL120Chain.base (allSteps Data.PSL120Chain.strongGenerators
        (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base))
      (allInvSteps Data.PSL120Chain.strongGenerators
        (pinvs 120 Data.PSL120Chain.strongGenerators) Data.PSL120Chain.base)
      Data.PSL120Chain.base (pcomp 120 Data.quotientConjugator
        (pcomp 120 (bTab (wordArrs Data.LWords)[j]!)
          (pinvCand 120 Data.quotientConjugator)))) = true := by
  obtain ⟨hF, hu, hlev, hs⟩ := psl_parts
  refine ⟨?_, allBelowN_iff.2 fun j hj => ?_⟩
  · unfold pisInv
    refine allBelowN_iff.2 fun x hx => ?_
    obtain ⟨u1, u2⟩ := hu x hx
    rw [uinv_get u1, u2]
    simp [u1]
  · have hj' : j < 2 := hj
    have hqs : Data.quotientConjugator.size = 120 := rfl
    have hG : ∀ y < 120, uG j y < 120 := by
      intro y _
      unfold uG
      by_cases h : (bL[j]!)[uI y]! < 120
      · exact (hu _ h).1
      · rw [getElem!_neg _ _ (by rw [hqs]; exact h)]
        decide
    rw [(b_parts.2 j hj').2]
    refine memFull3_sound (s := 12) (F := pF) (FI := pFI) (B := pB) (G := uG j) (IDX := pIDX)
      (LEN := pLEN) (Mr := pMr) (PTS := pPTS) (POS := pPOS) (PAR := pPAR) (LAB := pLAB) rfl
      (fun j' hj' x hx => hF j' hj' x hx) rfl (fun k hk => ?_) (fun y hy => ?_) hG
      (fun i hi => (hlev i hi).1) (fun i hi => (hlev i hi).2.1) (fun i hi => (hlev i hi).2.2.1)
      (fun i hi => (hlev i hi).2.2.2) (hs j hj')
    · interval_cases k <;> exact ⟨rfl, by decide⟩
    · rw [pcomp_get' hy, pcomp_get' hy, uinv_get hy]
      rfl

end CertificateChecks.KernelSpor.ON3

end

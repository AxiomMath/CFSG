module

public import Certificates.Kernel.SporSch.Co3.Bind12
public import Certificates.Kernel.Sporadic.Co3.C
public import CFSG.Certificates.Kernel.SporSch.F2MatSound
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import Certificates.Data.Kernel.Spor.M11
public import CFSG.Sporadic.Schreier.Co3FaithfulCheckInputs
public import CFSG.Sporadic.Schreier.Co3FaithfulData
public import Certificates.Data.CFSGNative.Co3.Data
meta import Certificates.Data.CFSGNative.Co3.Data
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.F2MatProved

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSporSch.Co3SeedA CFSG.Sporadic.Co3.Native.seedA

#ks_chars CertificateChecks.KernelSporSch.Co3SeedB CFSG.Sporadic.Co3.Native.seedB

namespace CertificateChecks.KernelSporSch.Co3Faith

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.M11
open CFSG.Sporadic.Schreier.Co3 CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch

@[expose] def RAP : Nat :=
  38645672441016520314695594408531194785678616703706560684571826479219934499680604398606132468445390448471854208560110006333556511740059239583245713

@[expose] def RBP : Nat :=
  11098834015679396170972097827249390772128120638480717935881162966344281754215353370336491775243136030446953134485798397426645350153017110451749034

@[expose] def SPP : Nat :=
  37438837689394882688394952967134520293723632393137869526598545445593305183404770115251997268926603930103117459341538090264811935802110915751335687

@[expose] noncomputable def FW (r : Nat) : Nat := pg 253 (mask 253) (Co3Forms.L r) 0

@[expose] noncomputable def IDXP : Nat := packL 9 co3DiffIdx

@[expose] noncomputable def DRK (j : Nat) : Nat :=
  Nat.xor (diagK (FW (pg 9 (mask 9) IDXP j))) (diagK (FW 0))

theorem ra : Nat.beq (payRun 22 Co3SeedA.chars 0 0 0) RAP = true := by quickRfl
theorem rb : Nat.beq (payRun 22 Co3SeedB.chars 0 0 0) RBP = true := by quickRfl

theorem dist : allN 276 (fun r => allN r (fun r' => bIf(Nat.beq (FW r) (FW r'), false, true))) =
    true := by quickRfl

theorem offs : allN 276 (fun r => offK (FW r) (FW 0)) = true := by quickRfl

@[expose] noncomputable def pullAt (R G r : Nat) : Bool :=
  strictB (pg 9 (mask 9) G r) (fun q => bAnd(Nat.blt q 276, pullK R (FW r) (FW q)))

theorem pa0 : allBlk 0 (pullAt RAP (Co3C.S 0)) 69 = true := by quickRfl
theorem pa1 : allBlk 69 (pullAt RAP (Co3C.S 0)) 69 = true := by quickRfl
theorem pa2 : allBlk 138 (pullAt RAP (Co3C.S 0)) 69 = true := by quickRfl
theorem pa3 : allBlk 207 (pullAt RAP (Co3C.S 0)) 69 = true := by quickRfl
theorem pb0 : allBlk 0 (pullAt RBP (Co3C.S 1)) 69 = true := by quickRfl
theorem pb1 : allBlk 69 (pullAt RBP (Co3C.S 1)) 69 = true := by quickRfl
theorem pb2 : allBlk 138 (pullAt RBP (Co3C.S 1)) 69 = true := by quickRfl
theorem pb3 : allBlk 207 (pullAt RBP (Co3C.S 1)) 69 = true := by quickRfl

theorem powA : Nat.beq (powP 22 RAP 3) (idP 22) = true := by quickRfl
theorem powB : Nat.beq (powP 22 RBP 4) (idP 22) = true := by quickRfl

theorem idx_from : bindFromK 9 IDXP co3DiffIdx 0 = true := by quickRfl
theorem idx_lt : allN 22 (fun j => Nat.blt (pg 9 (mask 9) IDXP j) 276) = true := by quickRfl
theorem drk_lt : allN 22 (fun j => Nat.blt (DRK j) 4194304) = true := by quickRfl
theorem sp_bind : bindListK 22 22 SPP co3SpanCoeffs.toList = true := by quickRfl
theorem span : Nat.beq (mulP 22 SPP (packR 22 DRK)) (idP 22) = true := by quickRfl

theorem blocks {f : Nat → Bool} (h0 : allBlk 0 f 69 = true) (h1 : allBlk 69 f 69 = true)
    (h2 : allBlk 138 f 69 = true) (h3 : allBlk 207 f 69 = true) (r : Nat) (hr : r < 276) :
    f r = true := by
  rcases Nat.lt_or_ge r 69 with a | a
  · have := allBlk_spec h0 r a
    simpa [Nat.add_eq] using this
  rcases Nat.lt_or_ge r 138 with b | b
  · have := allBlk_spec h1 (r - 69) (by omega)
    simpa [Nat.add_eq, Nat.add_sub_cancel' a] using this
  rcases Nat.lt_or_ge r 207 with c | c
  · have := allBlk_spec h2 (r - 138) (by omega)
    simpa [Nat.add_eq, Nat.add_sub_cancel' b] using this
  · have := allBlk_spec h3 (r - 207) (by omega)
    simpa [Nat.add_eq, Nat.add_sub_cancel' c] using this

theorem unpack_get {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [getElem!_pos _ i (by simp [unpack]; omega)]
  simp [unpack]

theorem rowsA_eq : CFSG.Sporadic.Co3.Native.co3Data.rowsA = unpack 22 22 RAP := by
  have e : CFSG.Sporadic.Co3.Native.co3Data.rowsA = rowsOfPayload 22 CFSG.Sporadic.Co3.Native.seedA :=
    rfl
  rw [e, Co3SeedA.eq, payRun_eq, Nat.eq_of_beq_eq_true ra]

theorem rowsB_eq : CFSG.Sporadic.Co3.Native.co3Data.rowsB = unpack 22 22 RBP := by
  have e : CFSG.Sporadic.Co3.Native.co3Data.rowsB = rowsOfPayload 22 CFSG.Sporadic.Co3.Native.seedB :=
    rfl
  rw [e, Co3SeedB.eq, payRun_eq, Nat.eq_of_beq_eq_true rb]

theorem sp_eq : co3SpanCoeffs = unpack 22 22 SPP := by
  have e : co3SpanCoeffs.toList.toArray = co3SpanCoeffs := Array.toArray_toList
  rw [← e]
  exact toArray_eq_of_bindListK sp_bind

theorem idx_get (j : Nat) (h : j < co3DiffIdx.length) :
    co3DiffIdx[j] = pg 9 (mask 9) IDXP j := by
  have := bindFromK_spec idx_from j h
  rwa [Nat.zero_add] at this

theorem diff_eq : co3DiffRows = unpack 22 22 (packR 22 DRK) := by
  rw [unpack_packR_proved fun i hi => Nat.blt_eq.mp (allN_spec drk_lt i hi)]
  apply Array.ext
  · simp [co3DiffRows, co3DiffIdx]
  · intro j h1 h2
    have hj : j < 22 := by simpa using h2
    simp only [co3DiffRows, List.getElem_toArray, List.getElem_map, Array.getElem_ofFn]
    have hl : j < co3DiffIdx.length := by simpa [co3DiffRows] using h1
    rw [idx_get j hl, Co3Forms.word_eq (Nat.blt_eq.mp (allN_spec idx_lt j hj)),
      Co3Forms.word_eq (by omega), ← diagK_eq_proved, ← diagK_eq_proved]
    rfl

theorem pull_of {R G : Nat} {g : Array Nat} {A : Array Nat} (hg : g = unpack 276 9 G)
    (hA : A = unpack 22 22 R) (h : ∀ r < 276, pullAt R G r = true) (r : Nat) (hr : r < 276) :
    g[r]! < 276 ∧ pullOK A (co3FormWord r) (co3FormWord g[r]!) = true := by
  have hq := h r hr
  unfold pullAt at hq
  rw [strictB_eq] at hq
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 hq
  have hlt := Nat.blt_eq.mp h1
  rw [hg, unpack_get hr, hA, Co3Forms.word_eq hr, Co3Forms.word_eq hlt]
  exact ⟨hlt, pullK_sound_proved h2⟩

theorem facts : ((∀ r < 276, ∀ r' < r, co3FormWord r ≠ co3FormWord r') ∧
      (∀ r < 276, offDiagOK (co3FormWord r) (co3FormWord 0) = true) ∧
      (∀ r < 276, (co3ChainArrs[0]!)[r]! < 276 ∧
        pullOK CFSG.Sporadic.Co3.Native.co3Data.rowsA (co3FormWord r)
          (co3FormWord (co3ChainArrs[0]!)[r]!) = true) ∧
      (∀ r < 276, (co3ChainArrs[1]!)[r]! < 276 ∧
        pullOK CFSG.Sporadic.Co3.Native.co3Data.rowsB (co3FormWord r)
          (co3FormWord (co3ChainArrs[1]!)[r]!) = true) ∧
      mulRows 22 co3SpanCoeffs co3DiffRows = idRows 22)
    ∧ (powRows 22 CFSG.Sporadic.Co3.Native.co3Data.rowsA 3 = idRows 22 ∧
      powRows 22 CFSG.Sporadic.Co3.Native.co3Data.rowsB 4 = idRows 22) := by
  refine ⟨⟨fun r hr r' hr' => ?_, fun r hr => ?_,
    pull_of (Co3C.binds.2.2.2.2.1 0 (by omega)) rowsA_eq (blocks pa0 pa1 pa2 pa3),
    pull_of (Co3C.binds.2.2.2.2.1 1 (by omega)) rowsB_eq (blocks pb0 pb1 pb2 pb3), ?_⟩, ?_, ?_⟩
  · rw [Co3Forms.word_eq hr, Co3Forms.word_eq (by omega)]
    intro he
    have hd := allN_spec (allN_spec dist r hr) r' hr'
    have hb : Nat.beq (FW r) (FW r') = true := by
      unfold FW
      rw [he]
      exact Nat.beq_refl _
    rw [hb] at hd
    exact Bool.false_ne_true hd
  · rw [Co3Forms.word_eq hr, Co3Forms.word_eq (by omega)]
    exact offK_sound_proved (allN_spec offs r hr)
  · rw [sp_eq, diff_eq, mulP_eq_proved, idP_eq_proved, Nat.eq_of_beq_eq_true span]
  · rw [rowsA_eq, powP_eq_proved, idP_eq_proved, Nat.eq_of_beq_eq_true powA]
  · rw [rowsB_eq, powP_eq_proved, idP_eq_proved, Nat.eq_of_beq_eq_true powB]

end CertificateChecks.KernelSporSch.Co3Faith

end

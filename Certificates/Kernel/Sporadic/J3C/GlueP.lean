module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Groups
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3CheckInputs
public import Certificates.Kernel.Sporadic.J3C.ChecksB
public import Certificates.Kernel.SchreierFam.J3CqLv
public import Certificates.Kernel.SchreierFam.J3CqBind
public import Certificates.Kernel.Sporadic.J3K.Final
public import CFSG.Certificates.Kernel.J3C.SoundU
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Normalizer
public import CFSG.Certificates.Kernel.MonsterB.Co2PermSound
public import CFSG.Certificates.Kernel.Spor.RawSiftK
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.Spor.PresCard
public import CFSG.Certificates.Kernel.Spor.SlpCard
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.Spor.PackWord
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.SchreierFam.All3Sound
public import CFSG.Certificates.Kernel.SchreierFam.CqKSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3CGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.CentReg CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.J3Data CFSG.Monster.B CFSG.Monster.B.Co2.Native CFSG.Sporadic.J3.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.J3K CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSchreierFam

theorem poaOfRep {t : Array Nat} {g : Equiv.Perm (Fin 20520)} (h : Co2.Rep 20520 t g) :
    Co2.permOfArr 20520 t = g := by
  have hc : (∀ i < 20520, t[i]! < 20520) ∧ ∀ i < 20520, ∀ j < 20520, t[i]! = t[j]! → i = j :=
    ⟨fun i hi => h.lt hi, fun i hi j hj hij => by
      rw [h.apply hi, h.apply hj] at hij
      have := g.injective (Fin.ext hij)
      simpa using this⟩
  ext x
  rw [Co2.permOfArr, dite_eq_left hc]
  change t[(x : ℕ)]! = _
  exact h x

theorem invAct {g : Equiv.Perm (Fin 20520)} {f fi : Nat → Nat}
    (hg : ∀ x < 20520, actN g x = f x) (hfi : ∀ x < 20520, fi x < 20520 ∧ fi (f x) = x) :
    ∀ x < 20520, actN g⁻¹ x = fi x := by
  intro x hx
  have h1 := actN_lt g⁻¹ hx
  have e : f (actN g⁻¹ x) = x := by rw [← hg _ h1, ← actN_mul, mul_inv_cancel, actN_one]
  calc actN g⁻¹ x = fi (f (actN g⁻¹ x)) := ((hfi _ h1).2).symm
    _ = fi x := by rw [e]

theorem eqASelf (t : Array Nat) : eqA 20520 t t = true := by
  unfold eqA
  rw [Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem aArr : abArr[0]! = Array.ofFn (n := 20520) fun x => r32 TA x.val := by
  have e : abArr[0]! = CFSG.Sporadic.SmallOddCore.Native.natArr (j3Data ()).tA := rfl
  rw [e, J3CqBind.tA_D]
  refine (J3CqBind.natArr_ofFn fun x hx => (J3K.pt_spec hx).2.1).trans ?_
  exact CFSG.KC.HexaStabK.unpack_pmk (by norm_num)
    fun x hx => lt_trans (J3K.pt_spec hx).2.1 (by norm_num)

theorem bArr : abArr[1]! = Array.ofFn (n := 20520) fun x => r32 TB x.val := by
  have e : abArr[1]! = CFSG.Sporadic.SmallOddCore.Native.natArr (j3Data ()).tB := rfl
  rw [e, J3CqBind.tB_D]
  refine (J3CqBind.natArr_ofFn fun x hx => (J3K.pt_spec hx).2.2.1).trans ?_
  exact CFSG.KC.HexaStabK.unpack_pmk (by norm_num)
    fun x hx => lt_trans (J3K.pt_spec hx).2.2.1 (by norm_num)

theorem aGet {x : Nat} (hx : x < 20520) : (abArr[0]!)[x]! = r32 TA x := by
  rw [aArr, Co2.getElem!_ofFn_nat _ hx]

theorem bGet {x : Nat} (hx : x < 20520) : (abArr[1]!)[x]! = r32 TB x := by
  rw [bArr, Co2.getElem!_ofFn_nat _ hx]

theorem isInvAB : ∀ h < 2, isInvA 20520 abArr[h]! abInv[h]! = true := by
  intro h hh
  have e : abInv[h]! = invCand 20520 abArr[h]! := J3CqBind.map_get _ _ (by
    have hs : abArr.size = 2 := rfl
    omega)
  rw [e]
  interval_cases h
  · refine CFSG.KC.Co2Mem.isInvA_invCand (fun i hi => ?_) (fun i j hi hj hij => ?_)
    · rw [aGet hi]
      exact (J3K.pt_spec hi).2.1
    · rw [aGet hi, aGet hj] at hij
      rw [← (inv_facts hi).2.1, ← (inv_facts hj).2.1, hij]
  · refine CFSG.KC.Co2Mem.isInvA_invCand (fun i hi => ?_) (fun i j hi hj hij => ?_)
    · rw [bGet hi]
      exact (J3K.pt_spec hi).2.2.1
    · rw [bGet hi, bGet hj] at hij
      rw [← (inv_facts hi).2.2.2, ← (inv_facts hj).2.2.2, hij]

theorem abRep : ∀ h < 2, Co2.Rep 20520 abArr[h]! (Co2.permOfArr 20520 abArr[h]!) :=
  fun h hh => (Co2.rep_permOfArr (isInvAB h hh)).1

theorem abInvRep : ∀ h < 2, Co2.Rep 20520 abInv[h]! (Co2.permOfArr 20520 abArr[h]!)⁻¹ :=
  fun h hh => (Co2.rep_permOfArr (isInvAB h hh)).2

theorem paMem : J3Groups.pa ∈ J3Groups.P := Subgroup.subset_closure (Set.mem_insert _ _)

theorem pbMem : J3Groups.pb ∈ J3Groups.P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem abMem : ∀ h < 2, Co2.permOfArr 20520 abArr[h]! ∈ J3Groups.P := by
  intro h hh
  interval_cases h
  · exact paMem
  · exact pbMem

theorem actPa : ∀ x < 20520, actN J3Groups.pa x = r32 TA x := fun x hx => by
  rw [actN_of_lt _ hx, ← aGet hx]
  exact ((abRep 0 (by norm_num)).apply hx).symm

theorem actPb : ∀ x < 20520, actN J3Groups.pb x = r32 TB x := fun x hx => by
  rw [actN_of_lt _ hx, ← bGet hx]
  exact ((abRep 1 (by norm_num)).apply hx).symm

theorem actPai : ∀ x < 20520, actN J3Groups.pa⁻¹ x = r32 J3K.AI x :=
  invAct actPa fun x hx => ⟨(inv_facts hx).1, (inv_facts hx).2.1⟩

theorem actPbi : ∀ x < 20520, actN J3Groups.pb⁻¹ x = r32 J3K.BI x :=
  invAct actPb fun x hx => ⟨(inv_facts hx).2.2.1, (inv_facts hx).2.2.2⟩

theorem paEq : J3Groups.pa = SC.permF 20520 (r32 TA) :=
  Equiv.ext fun x => Fin.ext (by rw [SC.permF_val permTA x, ← actN_fin, actPa _ x.isLt])

theorem pbEq : J3Groups.pb = SC.permF 20520 (r32 TB) :=
  Equiv.ext fun x => Fin.ext (by rw [SC.permF_val permTB x, ← actN_fin, actPb _ x.isLt])

theorem pEq : J3Groups.P = Subgroup.closure
    ({SC.permF 20520 (r32 TA), SC.permF 20520 (r32 TB)} : Set (Equiv.Perm (Fin 20520))) := by
  unfold J3Groups.P
  rw [paEq, pbEq]

theorem cardP : Nat.card J3Groups.P ≤ CNTJ 0 * CNTJ 1 := by
  have hf : Finite TauCeti.Sporadic.j3Presentation.Group :=
    Certificates.certificate9119.1
  have hP : TauCeti.Sporadic.j3Presentation.generatorCount = 2 := by
    simp [TauCeti.GroupPresentation.generatorCount, TauCeti.Sporadic.j3Presentation_generatorNames]
  have g0i := SC.permF_inv permTA (fun x hx => (inv_facts hx).1) fun x hx => (inv_facts hx).2.1
  have g1i := SC.permF_inv permTB (fun x hx => (inv_facts hx).2.2.1)
    fun x hx => (inv_facts hx).2.2.2
  have hr : ∀ v ∈ TauCeti.Sporadic.j3Presentation.relatorLetters,
      wordProd (img2 (SC.permF 20520 (r32 TA)) (SC.permF 20520 (r32 TB))) v = 1 := by
    intro v hv
    refine Equiv.ext fun x => Fin.ext ?_
    rw [SC.wordProd_val permTA permTB g0i g1i v x, rels_spec v hv x.val x.isLt]
    rfl
  rw [pEq]
  refine le_trans (CFSG.KS.Pres.card_closure_le _ hP hr) ?_
  refine le_trans Certificates.certificate9119.2 ?_
  decide

theorem sigP : ∀ l < 8, sig 20520 LT8 l ∈ J3Groups.P := by
  set KF := Subgroup.closure
    ({SC.permF 20520 (r32 TA), SC.permF 20520 (r32 TB)} : Set (Equiv.Perm (Fin 20520)))
  have iA := SC.permF_inv permTA (fun x hx => (inv_facts hx).1) fun x hx => (inv_facts hx).2.1
  have iB := SC.permF_inv permTB (fun x hx => (inv_facts hx).2.2.1)
    fun x hx => (inv_facts hx).2.2.2
  have hA : SC.permF 20520 (r32 TA) ∈ KF := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : SC.permF 20520 (r32 TB) ∈ KF := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hG : ∀ z : Int, z ≠ 0 → z.natAbs ≤ 2 →
      SC.PermF 20520 (GJ z) ∧ SC.permF 20520 (GJ z) ∈ KF := by
    intro z hz ha
    rcases (by omega : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) with rfl | rfl | rfl | rfl
    · have e : GJ 1 = r32 TA := by funext x; rfl
      rw [e]
      exact ⟨permTA, hA⟩
    · have e : GJ (-1) = r32 J3K.AI := by funext x; rfl
      rw [e, iA.2]
      exact ⟨iA.1, KF.inv_mem hA⟩
    · have e : GJ 2 = r32 TB := by funext x; rfl
      rw [e]
      exact ⟨permTB, hB⟩
    · have e : GJ (-2) = r32 J3K.BI := by funext x; rfl
      rw [e]
      refine ⟨iB.1, ?_⟩
      rw [iB.2]
      exact KF.inv_mem hB
  have hs : (j3Data ()).words.size = 4 := rfl
  have hmem := SC.slp_mem (K := KF) (G := GJ) (L := LJ) (words := (j3Data ()).words) hG words_ok
    (fun j hj x hx => word_spec (by omega) hx)
    (fun j hj x hx => ⟨(inv_spec (by omega) hx).2.1, (inv_spec (by omega) hx).2.2⟩)
  rw [hs] at hmem
  intro l hl
  obtain ⟨m1, m2⟩ := hmem l hl
  unfold sig
  rw [SC.permOfT_eq, ← (SC.permF_congr m1 fun x hx => (letters_get.2 l hl x hx).symm).2, pEq]
  exact m2

theorem rep0 : TBfs.Rep 20520 (BJ 0) (CNTJ 0) (lvK LJ BJ 8 0).length LJ (lvAt LJ BJ 8 0) (PTSJ 0)
    (POSJ 0) (PARJ 0) (LABJ 0) (TIJ 0) := rep_of chain_hyp (by norm_num)

theorem rep1 : TBfs.Rep 20520 (BJ 1) (CNTJ 1) (lvK LJ BJ 8 1).length LJ (lvAt LJ BJ 8 1) (PTSJ 1)
    (POSJ 1) (PARJ 1) (LABJ 1) (TIJ 1) := rep_of chain_hyp (by norm_num)

theorem lvLt {i t : Nat} (ht : t < (lvK LJ BJ 8 i).length) : lvAt LJ BJ 8 i t < 8 :=
  (mem_lvK.1 (lvAt_mem ht)).1

theorem hsig0 : ∀ t < (lvK LJ BJ 8 0).length, ∀ x < 20520,
    actN (sig 20520 LT8 (lvAt LJ BJ 8 0 t)) x = LJ (lvAt LJ BJ 8 0 t) x :=
  fun _ ht _ hx => actN_sig chain_hyp (lvLt ht) hx

theorem hsigi0 : ∀ t < (lvK LJ BJ 8 0).length, ∀ x < 20520,
    actN (sig 20520 LT8 (lvAt LJ BJ 8 0 t))⁻¹ x = LJ (Nat.xor (lvAt LJ BJ 8 0 t) 1) x := by
  intro t ht x hx
  rw [xor_one]
  exact actN_sig_inv chain_hyp (lvLt ht) hx

theorem hsig1 : ∀ t < (lvK LJ BJ 8 1).length, ∀ x < 20520,
    actN (sig 20520 LT8 (lvAt LJ BJ 8 1 t)) x = LJ (lvAt LJ BJ 8 1 t) x :=
  fun _ ht _ hx => actN_sig chain_hyp (lvLt ht) hx

theorem hP0 : ∀ t < (lvK LJ BJ 8 0).length, sig 20520 LT8 (lvAt LJ BJ 8 0 t) ∈ J3Groups.P :=
  fun _ ht => sigP _ (lvLt ht)

theorem hP1 : ∀ t < (lvK LJ BJ 8 1).length, sig 20520 LT8 (lvAt LJ BJ 8 1 t) ∈ J3Groups.P ∧
    sig 20520 LT8 (lvAt LJ BJ 8 1 t) (⟨BJ 0, root_lt rep0⟩ : Fin 20520) =
      ⟨BJ 0, root_lt rep0⟩ := by
  intro t ht
  refine ⟨sigP _ (lvLt ht), Fin.ext ?_⟩
  rw [sig_val chain_hyp (lvLt ht)]
  exact (mem_lvK.1 (lvAt_mem ht)).2 0 (by norm_num)

theorem centLe : Nat.card (centIn J3Groups.P J3Groups.pa) ≤ 1920 := by
  have h := centOK_sound rep0 rep1 hsig0 hsigi0 hsig1 hP0 hP1 cardP (A := r32 TA)
    (a := J3Groups.pa) (fun x hx => (actPa x hx).symm) cent16
  rw [Nat.eq_of_beq_eq_true fix120] at h
  exact h

end CertificateChecks.KernelSpor.J3CGlue

end

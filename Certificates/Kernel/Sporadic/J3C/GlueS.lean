module

public import Certificates.Kernel.Sporadic.J3C.GlueKC

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSpor.J3CGlue

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.CentReg CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.J3Data CFSG.Monster.B CFSG.Monster.B.Co2.Native CFSG.Sporadic.J3.Native
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.J3K CertificateChecks.KernelSpor.J3C
  CertificateChecks.KernelSchreierFam

@[expose] noncomputable def ς (i : Nat) : Equiv.Perm (Fin 20520) := Co2.permOfArr 20520 sStrong[i]!

theorem swOK : ∀ i < 4, lettersOK 2 sWordsK[i]! = true := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem ςEq : ∀ i < 4, ς i = wordP σK sWordsK[i]! := by
  intro i hi
  have e : sStrong[i]! = wordA 20520 kStrong kInv sWordsK[i]! :=
    J3CqBind.toArray_map_get _ _ (by rw [J3CqBind.sWords_len]; exact hi)
  unfold ς
  rw [e]
  exact poaOfRep (repWP _ (swOK i hi))

theorem sGetD : ∀ i < 4, List.getD sWordsK i [] = sWordsK[i]! := by
  intro i hi
  interval_cases i <;> rfl

theorem actS : ∀ i < 4, ∀ x < 20520, actN (ς i) x = SL i x := by
  intro i hi x hx
  rw [ςEq i hi]
  unfold SL
  rw [sGetD i hi]
  exact (wEval_eq actSK _ (sgnLt _ (swOK i hi)) x hx).symm

theorem ςK : ∀ i < 4, ς i ∈ J3Groups.K := by
  intro i hi
  rw [ςEq i hi]
  exact wordP_mem σKK (sgnLt _ (swOK i hi))

theorem ςS : ∀ i < 4, ς i ∈ J3Groups.S := fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem sK : J3Groups.S ≤ J3Groups.K := by
  unfold J3Groups.S J3Groups.gen
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact ςK i hi

theorem sRange : J3Groups.S ≤ Subgroup.closure (Set.range fun t : Fin 4 => ς t.val) := by
  unfold J3Groups.S J3Groups.gen
  rw [Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem repTS : TBfs.Rep 20520 0 TS.cnt 4 SL (fun t => t) TS.PTS TS.POS TS.PAR TS.LAB TS.TI :=
  ⟨TBfs.hd_spec tsHd, fun k hk => TBfs.pt_spec (Raw.Orb.allN_iff.1 tsPt k hk)⟩

theorem sFree : Nat.card J3Groups.S = TS.cnt ∧ ∀ g ∈ J3Groups.S, ∃ k < TS.cnt,
    r32 TS.PTS k = (g (⟨0, root_lt repTS⟩ : Fin 20520) : Nat) ∧ g = tw ς TS.PAR TS.LAB k :=
  card_of_free repTS actS ςS (fun _ hg => tree_closed repTS actS (sRange hg))
    (fun g hg => kFree.2.2 g (sK hg))

theorem sCard : Nat.card J3Groups.S = 128 := by
  rw [sFree.1, Nat.eq_of_beq_eq_true tsCnt]

@[expose] noncomputable def σAB (l : Nat) : Equiv.Perm (Fin 20520) :=
  if l = 0 then J3Groups.pa else if l = 1 then J3Groups.pa⁻¹ else if l = 2 then J3Groups.pb
    else J3Groups.pb⁻¹

theorem σAB0 : σAB 0 = J3Groups.pa := by
  unfold σAB
  rw [if_pos rfl]

theorem σAB1 : σAB 1 = J3Groups.pa⁻¹ := by
  unfold σAB
  rw [if_neg (by decide), if_pos rfl]

theorem σAB2 : σAB 2 = J3Groups.pb := by
  unfold σAB
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem σAB3 : σAB 3 = J3Groups.pb⁻¹ := by
  unfold σAB
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem abr0 (x : Nat) : ABr 0 x = r32 TA x := by
  unfold ABr
  rfl

theorem abr1 (x : Nat) : ABr 1 x = r32 J3K.AI x := by
  unfold ABr
  rfl

theorem abr2 (x : Nat) : ABr 2 x = r32 TB x := by
  unfold ABr
  rfl

theorem abr3 (x : Nat) : ABr 3 x = r32 J3K.BI x := by
  unfold ABr
  rfl

theorem actAB : ∀ l < 4, ∀ x < 20520, actN (σAB l) x = ABr l x := by
  intro l hl x hx
  interval_cases l
  · rw [σAB0, abr0]
    exact actPa x hx
  · rw [σAB1, abr1]
    exact actPai x hx
  · rw [σAB2, abr2]
    exact actPb x hx
  · rw [σAB3, abr3]
    exact actPbi x hx

theorem actABi : ∀ l < 4, ∀ x < 20520, actN (σAB l)⁻¹ x = ABr (Nat.xor l 1) x := by
  intro l hl x hx
  interval_cases l
  · have e : Nat.xor 0 1 = 1 := rfl
    rw [σAB0, e, abr1]
    exact actPai x hx
  · have e : Nat.xor 1 1 = 0 := rfl
    rw [σAB1, e, abr0, inv_inv]
    exact actPa x hx
  · have e : Nat.xor 2 1 = 3 := rfl
    rw [σAB2, e, abr3]
    exact actPbi x hx
  · have e : Nat.xor 3 1 = 2 := rfl
    rw [σAB3, e, abr2, inv_inv]
    exact actPb x hx

theorem abP : ∀ l < 4, σAB l ∈ J3Groups.P := by
  intro l hl
  interval_cases l
  · rw [σAB0]
    exact paMem
  · rw [σAB1]
    exact J3Groups.P.inv_mem paMem
  · rw [σAB2]
    exact pbMem
  · rw [σAB3]
    exact J3Groups.P.inv_mem pbMem

theorem cwLt : ∀ j < TS.cnt, ∀ z ∈ CW j, sgnL z < 4 := by
  intro j _ z hz
  unfold CW at hz
  rw [List.getD_eq_getElem?_getD] at hz
  cases h : conjWordsAB[r32 CI j]? with
  | none =>
    rw [h] at hz
    simp at hz
  | some w =>
    rw [h, Option.getD_some] at hz
    obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 h
    have hw := List.all_eq_true.1 cwLet w (by rw [← e]; exact List.getElem_mem hi)
    have := List.all_eq_true.1 hw z hz
    exact Nat.blt_eq.mp this

theorem fixP2 : ∀ g ∈ J3Groups.P, g (⟨0, root_lt repTS⟩ : Fin 20520) = ⟨0, root_lt repTS⟩ →
    g (⟨1, by norm_num⟩ : Fin 20520) = ⟨1, by norm_num⟩ → g = 1 :=
  fun g hg h0 h1 => fix2_of_two_level rep0 rep1 hsig0 hsig1 hP0 hP1 cardP g hg h0 h1

theorem coverS' : ∀ s ∈ J3Groups.S, orderOf s = 2 → ∃ c ∈ J3Groups.P, s = c * J3Groups.pa * c⁻¹ :=
  fun _ hs ho => by
    have h := coverK_sound repTS actS sFree.2 (G := ABr) (γ := σAB) (NL := 4) (a0 := 0) (b := 1)
      (W := CW) actAB actABi abP cwLt (by norm_num) (by norm_num) (sK.trans kP) fixP2 cover hs ho
    rw [σAB0] at h
    exact h

theorem sSizes : CFSG.Certificates.Native.rawOrbitSizes 20520 sStrong sBase = [128, 1, 1] := by
  rw [CFSG.KS.Raw.Orb.rawOrbitSizes_of_K J3CqBind.s_binds J3CqBind.sy_perm J3Cq.SY.hl]
  have e0 := Nat.eq_of_beq_eq_true J3Cq.rc0
  have e1 := Nat.eq_of_beq_eq_true rc1
  have e2 := Nat.eq_of_beq_eq_true rc2
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [hr, List.map_cons, List.map_nil, e0, e1, e2]

end CertificateChecks.KernelSpor.J3CGlue

end

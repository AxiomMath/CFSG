module

public import Certificates.Kernel.TcGen.McL
public import Certificates.Kernel.TcGen.Suz
public import Certificates.Kernel.TcGen.Fi22
public import Certificates.Kernel.TcGen.ON
public import CFSG.Certificates.Kernel.OpsLayMcertSound
public import CFSG.Certificates.Kernel.OpsLayTabSound
public import Certificates.Data.CFSGNative.CTP.StrongP
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.Kernel.OpsLayDerSound
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFillSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3 CFSG.Blueprint
open CFSG.KC.OpsLayK.Snd (runL)

theorem tc3_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : TSpec} (hw : D.wf = true) (h : seedsL c A B ⟨n, prog, D.facts⟩ D.rA D.rB = true) :
    tcCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨hm, hrA, hrB, h0, h1⟩ := seedsL_sound hc hp hd hA hB hsA hsB h
  dsimp only at hrA hrB h0 h1
  unfold tcCheck
  rw [hm, decide_eq_true hrA, decide_eq_true hrB, h0, h1, hw]
  rfl

theorem cp3_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : CpSpec} (hw : D.wf = true) (h : seedsL c A B ⟨n, prog, D.facts⟩ D.rA D.rB = true) :
    cpCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨hm, hrA, hrB, h0, h1⟩ := seedsL_sound hc hp hd hA hB hsA hsB h
  dsimp only at hrA hrB h0 h1
  unfold cpCheck
  rw [hm, decide_eq_true hrA, decide_eq_true hrB, h0, h1, hw]
  rfl

theorem tc3C_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : TSpec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {S : Nat → List Nat} {k m kf mf : Nat} (h0 : S 0 = initR c A B n)
    (hm : prog.length ≤ m * k) (hch : ∀ i < m, chunkL c prog k i (S i) (S (i + 1)) = true)
    (hmf : D.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c (S m) n D.facts kf i = true)
    (he : seedRegsL c (S m) A B D.rA D.rB = true) :
    tcCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨hm', hrA', hrB', h0', h1'⟩ := seedsLC_sound (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB
    hsA hsB hprog hrA hrB h0 hm hch hmf hf he
  dsimp only at hrA' hrB' h0' h1'
  unfold tcCheck
  rw [hm', decide_eq_true hrA', decide_eq_true hrB', h0', h1', hw]
  rfl

theorem cp3C_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : CpSpec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {S : Nat → List Nat} {k m kf mf : Nat} (h0 : S 0 = initR c A B n)
    (hm : prog.length ≤ m * k) (hch : ∀ i < m, chunkL c prog k i (S i) (S (i + 1)) = true)
    (hmf : D.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c (S m) n D.facts kf i = true)
    (he : seedRegsL c (S m) A B D.rA D.rB = true) :
    cpCheck (ops3 d) sA sB n prog D = true := by
  obtain ⟨hm', hrA', hrB', h0', h1'⟩ := seedsLC_sound (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB
    hsA hsB hprog hrA hrB h0 hm hch hmf hf he
  dsimp only at hrA' hrB' h0' h1'
  unfold cpCheck
  rw [hm', decide_eq_true hrA', decide_eq_true hrB', h0', h1', hw]
  rfl

theorem tc3T_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : TSpec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {S : List Nat} {kf mf : Nat} (hrun : runL c prog (initR c A B n) = S)
    (hmf : D.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c S n D.facts kf i = true)
    (he : seedRegsL c S A B D.rA D.rB = true) :
    tcCheck (ops3 d) sA sB n prog D = true := by
  subst hrun
  obtain ⟨hm', hrA', hrB', h0', h1'⟩ := seeds_of_runL (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB
    hsA hsB hprog hrA hrB (all_of_chunks hmf hf) he
  dsimp only at hrA' hrB' h0' h1'
  unfold tcCheck
  rw [hm', decide_eq_true hrA', decide_eq_true hrB', h0', h1', hw]
  rfl

theorem cp3T_of {c : Lay} {d A B : Nat} {LA LB : List Char} {sA sB : String}
    (hc : c.ok = true) (hp : c.p = 3) (hd : c.d = d)
    (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    {D : CpSpec} (hw : D.wf = true) (hprog : progOK n prog = true) (hrA : D.rA < n)
    (hrB : D.rB < n) {S : List Nat} {kf mf : Nat} (hrun : runL c prog (initR c A B n) = S)
    (hmf : D.facts.length ≤ mf * kf) (hf : ∀ i < mf, factsL c S n D.facts kf i = true)
    (he : seedRegsL c S A B D.rA D.rB = true) :
    cpCheck (ops3 d) sA sB n prog D = true := by
  subst hrun
  obtain ⟨hm', hrA', hrB', h0', h1'⟩ := seeds_of_runL (C := ⟨n, prog, D.facts⟩) hc hp hd hA hB
    hsA hsB hprog hrA hrB (all_of_chunks hmf hf) he
  dsimp only at hrA' hrB' h0' h1'
  unfold cpCheck
  rw [hm', decide_eq_true hrA', decide_eq_true hrB', h0', h1', hw]
  rfl

theorem cert9417 :
    (tcCheck (ops3 21) mclSylow5Data.seedA mclSylow5Data.seedB McLThree.tcNregs McLThree.tcProg
      McLThree.tcSpec = true) ∧
    (cpCheck (ops3 21) mclSylow5Data.seedA mclSylow5Data.seedB McLThree.cpNregs McLThree.cpProg
      McLThree.cpSpec = true) ∧ (McLThree.cpSpec.noFun = true) := by
  have hsA : mclSylow5Data.seedA = String.ofList McL.LA :=
    (rfl : mclSylow5Data.seedA = NativeSporadic.McLSeed1).trans McL.LA_eq
  have hsB : mclSylow5Data.seedB = String.ofList McL.LB :=
    (rfl : mclSylow5Data.seedB = NativeSporadic.McLSeed2).trans McL.LB_eq
  exact ⟨tc3_of McL.lay_ok rfl rfl McL.decA McL.decB hsA hsB (by decide +kernel) McL.tc_K,
    cp3_of McL.lay_ok rfl rfl McL.decA McL.decB hsA hsB (by decide +kernel) McL.cp_K,
    by decide +kernel⟩

theorem cert9500 :
    (tcCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 SuzThree.tcNregs
      SuzThree.tcProg SuzThree.tcSpec = true) ∧
    (cpCheck (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 SuzThree.cpNregs
      SuzThree.cpProg SuzThree.cpSpec = true) ∧ (SuzThree.cpSpec.noFun = true) :=
  ⟨tc3_of Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq (by decide +kernel) Suz.tc_K,
    cp3_of Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq (by decide +kernel) Suz.cp_K,
    by decide +kernel⟩

theorem cert9501 :
    (tcCheck (ops3 77) NativeSporadic.Fi22Seed1 NativeSporadic.Fi22Seed2 Fi22Three.tcNregs
      Fi22Three.tcProg Fi22Three.tcSpec = true) ∧
    (cpCheck (ops3 77) NativeSporadic.Fi22Seed1 NativeSporadic.Fi22Seed2 Fi22Three.cpNregs
      Fi22Three.cpProg Fi22Three.cpSpec = true) ∧ (Fi22Three.cpSpec.noFun = true) :=
  ⟨tc3_of Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB Fi22.LA_eq Fi22.LB_eq (by decide +kernel)
      Fi22.tc_K,
    cp3_of Fi22.lay_ok rfl rfl Fi22.decA Fi22.decB Fi22.LA_eq Fi22.LB_eq (by decide +kernel)
      Fi22.cp_K,
    by decide +kernel⟩

theorem factsL_of_L1 {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {A B : Nat}
    {LA LB : List Char} {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {prog : List Op}
    (hprog : progOK n prog = true) {S : List Nat} (hrun : runL c prog (initR c A B n) = S)
    {fs : List MFact} {K : List Nat} (hin : fs.all (factIn K) = true) {k i : Nat}
    (h : ((fs.drop (i * k)).take k).all (factL1 c S n) = true) : factsL c S n fs k i = true := by
  subst hrun
  have hL := CFSG.KC.OpsLayK.Snd.lcorr_regs hc hp hA hB hsA hsB hprog
  have hK : ∀ r ∈ K,
      CFSG.KS.Ord.Canon c.p c.d c.w (getR c (runL c prog (initR c A B n)) r) := by
    intro r _
    by_cases hrn : r < (runL c prog (initR c A B n)).length
    · exact (hL.2 r hrn).1
    · have e : getR c (runL c prog (initR c A B n)) r = c.ONE := by
        unfold getR
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      rw [e]
      exact (CFSG.KC.OpsLayK.Snd.rel_one hc hp).1
  unfold factsL
  rw [List.all_eq_true] at h hin ⊢
  intro f hf
  exact factL_of_factL1 hc hp hK f (hin f (List.mem_of_mem_drop (List.mem_of_mem_take hf)))
    (h f hf)

theorem TSpec.facts_split (D : TSpec) : ∀ f ∈ D.facts,
    f ∈ ({ D with der := [] }.facts ++ D.der.map fun d => .ord d.reg d.ord) ∨
      ∃ e ∈ D.der, f = .eq [(e.reg, 1)] e.w := by
  intro f hf
  rw [TSpec.facts, List.mem_append] at hf
  rcases hf with hf | hf
  · left
    apply List.mem_append_left
    simpa only [TSpec.facts, List.flatMap_nil, List.append_nil] using hf
  · obtain ⟨e, he, hfe⟩ := List.mem_flatMap.1 hf
    simp only [Der.facts, List.mem_cons, List.not_mem_nil, or_false] at hfe
    rcases hfe with rfl | rfl
    · exact Or.inl (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩))
    · exact Or.inr ⟨e, he, rfl⟩

theorem CpSpec.facts_split (D : CpSpec) : ∀ f ∈ D.facts,
    f ∈ ({ D with der := [] }.facts ++ D.der.map fun d => .ord d.reg d.ord) ∨
      ∃ e ∈ D.der, f = .eq [(e.reg, 1)] e.w := by
  intro f hf
  rw [CpSpec.facts, List.mem_append] at hf
  rcases hf with hf | hf
  · left
    apply List.mem_append_left
    simpa only [CpSpec.facts, List.flatMap_nil, List.append_nil] using hf
  · obtain ⟨e, he, hfe⟩ := List.mem_flatMap.1 hf
    simp only [Der.facts, List.mem_cons, List.not_mem_nil, or_false] at hfe
    rcases hfe with rfl | rfl
    · exact Or.inl (List.mem_append_right _ (List.mem_map.2 ⟨e, he, rfl⟩))
    · exact Or.inr ⟨e, he, rfl⟩

theorem factsL_of_der {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {A B : Nat}
    {LA LB : List Char} {sA sB : String} (hA : decOK c A LA = true) (hB : decOK c B LB = true)
    (hsA : sA = String.ofList LA) (hsB : sB = String.ofList LB) {n : Nat} {pre prog : List Op}
    {s : Nat} {ds : List Der} {av : List Nat} (hsplit : prog = pre ++ derProg s ds)
    (hpre : progOK n pre = true) {S : List Nat} (hrun : runL c prog (initR c A B n) = S)
    (hchk : derChk n s av ds = true) {fs fs' : List MFact}
    (hfs : ∀ f ∈ fs, f ∈ fs' ∨ ∃ e ∈ ds, f = .eq [(e.reg, 1)] e.w)
    (h' : fs'.all (factL c S n) = true) : ∀ i < 1, factsL c S n fs fs.length i = true := by
  intro i hi
  obtain rfl : i = 0 := by omega
  subst hrun hsplit
  have hL := CFSG.KC.OpsLayK.Snd.lcorr_regs (prog := pre) hc hp hA hB hsA hsB hpre
  have hR : ∀ r, CFSG.KS.Ord.Canon c.p c.d c.w (getR c (runL c pre (initR c A B n)) r) := by
    intro r
    by_cases hrn : r < (runL c pre (initR c A B n)).length
    · exact (hL.2 r hrn).1
    · have e : getR c (runL c pre (initR c A B n)) r = c.ONE := by
        unfold getR
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
      rw [e]
      exact (CFSG.KC.OpsLayK.Snd.rel_one hc hp).1
  have hD := der_eq_facts hc hp ds av _ hR (CFSG.KC.OpsLayK.Snd.runL_initR_length c pre A B n) hchk
  rw [← derRunL_append] at hD
  unfold factsL
  rw [Nat.zero_mul, List.drop_zero, List.take_length, List.all_eq_true]
  intro f hf
  rcases hfs f hf with h | ⟨e, he, rfl⟩
  · exact List.all_eq_true.1 h' f h
  · exact hD e he

namespace ON

theorem tab : ∀ v, 2 < v → v < C.N →
    CFSG.KC.OpsLayTab.entF lay.mul (powK lay) C.VT (CFSG.KC.OpsLayTab.keyAt C.KT v) v = true := by
  refine CFSG.KC.OpsLayTab.tab_of_chunksF (m := 35) (k := 64) (by decide) fun i hi => ?_
  interval_cases i
  exacts [tabC0, tabC1, tabC2, tabC3, tabC4, tabC5, tabC6, tabC7, tabC8, tabC9, tabC10, tabC11,
    tabC12, tabC13, tabC14, tabC15, tabC16, tabC17, tabC18, tabC19, tabC20, tabC21, tabC22, tabC23,
    tabC24, tabC25, tabC26, tabC27, tabC28, tabC29, tabC30, tabC31, tabC32, tabC33, tabC34]

theorem run_of_symP {prog : List Op} {VS S : List Nat} {I0 IF n : Nat}
    (h : symP prog VS I0 IF S n = true) : runL lay prog (initR lay A B n) = S := by
  unfold symP at h
  simp only [Bool.and_eq_true] at h
  rw [← eq_of_eqL h.1.2, CFSG.KC.OpsLayTab.runL_of_symF tab _ _ _ _ h.1.1, eq_of_eqL h.2]

theorem tcFa_all : ∀ i < 11, tcFa i = true := by
  intro i hi
  interval_cases i
  exacts [tcFa0, tcFa1, tcFa2, tcFa3, tcFa4, tcFa5, tcFa6, tcFa7, tcFa8, tcFa9, tcFa10]

theorem cpFa_all : ∀ i < 7, cpFa i = true := by
  intro i hi
  interval_cases i
  exacts [cpFa0, cpFa1, cpFa2, cpFa3, cpFa4, cpFa5, cpFa6]

theorem tcSplit : ONThree.tcProg = ONThree.tcProg.take 720 ++ derProg 2 ONThree.tcSpec.der :=
  eq_of_opsEqB (by decide +kernel)

theorem cpSplit : ONThree.cpProg = ONThree.cpProg.take 783 ++ derProg 2 ONThree.cpSpec.der :=
  eq_of_opsEqB (by decide +kernel)

theorem tcAll : tcFs.all (factL lay (T.SL.getD 11 []) ONThree.tcNregs) = true :=
  all_of_chunks (m := 11) (k := 12) (by decide +kernel) fun i hi =>
    factsL_of_L1 lay_ok rfl decA decB LA_eq LB_eq (by decide +kernel) (run_of_symP tcSym)
      (K := List.range ONThree.tcNregs) (by decide +kernel) (tcFa_all i hi)

theorem cpAll : cpFs.all (factL lay (C.SL.getD 11 []) ONThree.cpNregs) = true :=
  all_of_chunks (m := 7) (k := 12) (by decide +kernel) fun i hi =>
    factsL_of_L1 lay_ok rfl decA decB LA_eq LB_eq (by decide +kernel) (run_of_symP cpSym)
      (K := List.range ONThree.cpNregs) (by decide +kernel) (cpFa_all i hi)

end ON

theorem cert9504 :
    (tcCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 ONThree.tcNregs
      ONThree.tcProg ONThree.tcSpec = true) ∧
    (cpCheck (ops3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 ONThree.cpNregs
      ONThree.cpProg ONThree.cpSpec = true) ∧ (ONThree.cpSpec.noFun = true) :=
  ⟨tc3T_of (mf := 1) ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (ON.run_of_symP ON.tcSym) (Nat.le_of_eq (Nat.one_mul _).symm)
      (factsL_of_der ON.lay_ok rfl ON.decA ON.decB ON.LA_eq ON.LB_eq
        (av := ONThree.tcSpec.actRegs) ON.tcSplit
        (by decide +kernel) (ON.run_of_symP ON.tcSym) (by decide +kernel)
        (TSpec.facts_split _) ON.tcAll) ON.tcSeeds,
    cp3T_of (mf := 1) ON.lay_ok rfl rfl ON.decA ON.decB ON.LA_eq ON.LB_eq
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (ON.run_of_symP ON.cpSym) (Nat.le_of_eq (Nat.one_mul _).symm)
      (factsL_of_der ON.lay_ok rfl ON.decA ON.decB ON.LA_eq ON.LB_eq
        (av := ONThree.cpSpec.actRegs) ON.cpSplit
        (by decide +kernel) (ON.run_of_symP ON.cpSym) (by decide +kernel)
        (CpSpec.facts_split _) ON.cpAll) ON.cpSeeds,
    by decide +kernel⟩

end CertificateChecks.KernelTc

end

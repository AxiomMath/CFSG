module

public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.OpsLayMcertSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc

open CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.AGLEmbedding.R3 CFSG.Blueprint

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

namespace Fi23

theorem tcCh_all : ∀ i < 6, tcCh i = true := by
  intro i hi
  interval_cases i
  exacts [tcCh0, tcCh1, tcCh2, tcCh3, tcCh4, tcCh5]

theorem tcFa_all : ∀ i < 10, tcFa i = true := by
  intro i hi
  interval_cases i
  exacts [tcFa0, tcFa1, tcFa2, tcFa3, tcFa4, tcFa5, tcFa6, tcFa7, tcFa8, tcFa9]

theorem cpCh_all : ∀ i < 5, cpCh i = true := by
  intro i hi
  interval_cases i
  exacts [cpCh0, cpCh1, cpCh2, cpCh3, cpCh4]

theorem cpFa_all : ∀ i < 6, cpFa i = true := by
  intro i hi
  interval_cases i
  exacts [cpFa0, cpFa1, cpFa2, cpFa3, cpFa4, cpFa5]

end Fi23

theorem cert9507 :
    (tcCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2 Fi23Three.tcNregs
      Fi23Three.tcProg Fi23Three.tcSpec = true) ∧
    (cpCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2 Fi23Three.cpNregs
      Fi23Three.cpProg Fi23Three.cpSpec = true) ∧ (Fi23Three.cpSpec.noFun = true) :=
  ⟨tc3C_of (S := fun i => Fi23.T.SL.getD i []) (k := 200) (kf := 25) Fi23.lay_ok rfl rfl
      Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (eq_of_eqL Fi23.tcInit) (by decide +kernel)
      Fi23.tcCh_all (by decide +kernel) Fi23.tcFa_all Fi23.tcSeeds,
    cp3C_of (S := fun i => Fi23.C.SL.getD i []) (k := 200) (kf := 25) Fi23.lay_ok rfl rfl
      Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (eq_of_eqL Fi23.cpInit) (by decide +kernel)
      Fi23.cpCh_all (by decide +kernel) Fi23.cpFa_all Fi23.cpSeeds,
    by decide +kernel⟩

end CertificateChecks.KernelTc

end

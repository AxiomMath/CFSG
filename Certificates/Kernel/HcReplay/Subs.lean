module

public import Certificates.Data.Kernel.HcClos
public import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.HcReplayStep

public section

namespace CFSG.KC.HcPack

@[expose] def cA0 : ℕ := 1459489772190472173560349220849168662699482027105
@[expose] def cA1 : ℕ := 1133210907958796891996611681291775908598762440832
@[expose] def cA2 : ℕ := 1459957104930169070366788001133702281052641597602
@[expose] def cA3 : ℕ := 945283157430205989154843984332446948760502770720
@[expose] def cA4 : ℕ := 1459746573682848692498805938276209674371466303584
@[expose] def cA0I : ℕ := 1459802287035362921683008101000308218513723532291
@[expose] def cA1I : ℕ := 1364122364031551726010219206373941382942136109408
@[expose] def cA2I : ℕ := 1459972453025941830183551456764569644534127395270
@[expose] def cA3I : ℕ := 1316887607405542101115088452620304969528701470752
@[expose] def cZ : ℕ := 1415644244717357744752181898886272409354489712042
@[expose] def cYp : ℕ := 1459466053148750079268234941975840981864217131301
@[expose] def cYpI : ℕ := 1459793916088748851396454797421510527286557215952
@[expose] def cYm : ℕ := 1459481401243899803828718111059258225225618359822
@[expose] def cYmI : ℕ := 1459778567992768319367995617343474443901048373321

@[expose] def gH1 : List ℕ := [cA0, cA1, cA0I, cA1I]
@[expose] def gH2 : List ℕ := [cA2, cA3, cA2I, cA3I]
@[expose] def gK : List ℕ := [cA0, cA1, cA2, cA3, cA0I, cA1I, cA2I, cA3I]
@[expose] def gP : List ℕ := [cA0, cA2, cA0I, cA2I]
@[expose] def gS1 : List ℕ := [cA0, cA0I]
@[expose] def gS2 : List ℕ := [cA2, cA2I]
@[expose] def gYp : List ℕ := [cYp, cYpI]
@[expose] def gYm : List ℕ := [cYm, cYmI]
@[expose] def gC1 : List ℕ := [cA0, cA2, cA3, cA0I, cA2I, cA3I]
@[expose] def gC2 : List ℕ := [cA2, cA0, cA1, cA2I, cA0I, cA1I]
@[expose] def gN1 : List ℕ := [cA0, cA2, cA3, cA4, cA0I, cA2I, cA3I, cA4]
@[expose] def gN2 : List ℕ := [cA2, cA0, cA1, cA4, cA2I, cA0I, cA1I, cA4]
@[expose] def gPZ : List ℕ := [cA0, cA2, cZ, cA0I, cA2I, cZ]
@[expose] def gPE : List ℕ := [cA0, cA2, cA4, cZ, cA0I, cA2I, cA4, cZ]
@[expose] def gL1 : List ℕ := [cA0, cZ, cA0I, cZ]
@[expose] def gL2 : List ℕ := [cA2, cZ, cA2I, cZ]
@[expose] def gT1 : List ℕ := [cA0, cA1, cA4, cA0I, cA1I, cA4]
@[expose] def gT2 : List ℕ := [cA2, cA3, cA4, cA2I, cA3I, cA4]

end CFSG.KC.HcPack

#kc_eval CFSG.KC.HcPack clH1 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gH1
#kc_eval CFSG.KC.HcPack clH2 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gH2
#kc_eval CFSG.KC.HcPack clK CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gK
#kc_eval CFSG.KC.HcPack clP CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gP
#kc_eval CFSG.KC.HcPack clS1 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gS1
#kc_eval CFSG.KC.HcPack clS2 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gS2
#kc_eval CFSG.KC.HcPack clYp CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gYp
#kc_eval CFSG.KC.HcPack clYm CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gYm
#kc_eval CFSG.KC.HcPack clC1 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gC1
#kc_eval CFSG.KC.HcPack clC2 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gC2
#kc_eval CFSG.KC.HcPack clN1 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gN1
#kc_eval CFSG.KC.HcPack clN2 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gN2
#kc_eval CFSG.KC.HcPack clPZ CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gPZ
#kc_eval CFSG.KC.HcPack clPE CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gPE
#kc_eval CFSG.KC.HcPack clL1 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gL1
#kc_eval CFSG.KC.HcPack clL2 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gL2
#kc_eval CFSG.KC.HcPack clT1 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gT1
#kc_eval CFSG.KC.HcPack clT2 CFSG.KC.HcPack.Step.bfsRec 576 600
  1459980823972598128486511383358617792788444579872 gT2

namespace CFSG.KC.HcPack

@[expose] noncomputable def subR : List (List ℕ × List ℕ × List ℕ × List ℕ) :=
  [(gH1, clH1.E, clH1.ds, clH1.ord), (gH2, clH2.E, clH2.ds, clH2.ord),
    (gK, clK.E, clK.ds, clK.ord), (gP, clP.E, clP.ds, clP.ord),
    (gS1, clS1.E, clS1.ds, clS1.ord), (gS2, clS2.E, clS2.ds, clS2.ord),
    (gYp, clYp.E, clYp.ds, clYp.ord), (gYm, clYm.E, clYm.ds, clYm.ord),
    (gC1, clC1.E, clC1.ds, clC1.ord), (gC2, clC2.E, clC2.ds, clC2.ord),
    (gN1, clN1.E, clN1.ds, clN1.ord), (gN2, clN2.E, clN2.ds, clN2.ord),
    (gPZ, clPZ.E, clPZ.ds, clPZ.ord), (gPE, clPE.E, clPE.ds, clPE.ord),
    (gL1, clL1.E, clL1.ds, clL1.ord), (gL2, clL2.E, clL2.ds, clL2.ord),
    (gT1, clT1.E, clT1.ds, clT1.ord), (gT2, clT2.E, clT2.ds, clT2.ord)]

@[expose] noncomputable def subRow (i : ℕ) : List ℕ × List ℕ × List ℕ × List ℕ :=
  subR.getD i ([], [], [], [])

theorem subR_replay : ∀ i : Fin 18,
    replayB mulP 576 600 (subRow i).1 (subRow i).2.1 (subRow i).2.2.1 (subRow i).2.2.2
      1459980823972598128486511383358617792788444579872 = true := by
  decide +kernel

theorem subR_clos : ∀ i : Fin 8,
    closB mulP (getT (ofT (subRow i).2.1.length (subRow i).2.1)) (subRow i).2.1.length
      (subRow i).1 (subRow i).2.1 (subRow i).2.2.1 = true := by
  decide +kernel

theorem subR_clos_neg :
    closB mulP (getT (ofT clH1.E.length clH1.E)) clH1.E.length gH1 clH1.E (0 :: clH1.ds.tail) =
      false := by
  decide +kernel

end CFSG.KC.HcPack

end

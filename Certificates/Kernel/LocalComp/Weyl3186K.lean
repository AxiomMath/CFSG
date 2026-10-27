module

public import Certificates.Data.Kernel.WeylE8.TList
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3186

open CFSG.KC.Enum CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight.Weyl

@[expose] noncomputable def PP : Nat := nat_lit 49189901056771805163777032050271704160866777100133877122352252041159968830604897700273152006537536225338744684107182510864828605913972295971924732671232169244117002084301162652872747754789019872837514617979708299340473399328353328683838610449907067592813276172960363410294710429366595301105995800743247022092330248743157359783566343160283906574650838495553186857574846214756534124708648060771944014368841154492899363239504166619278823995386224296019189858748040

@[expose] noncomputable def MT : Nat := nat_lit 1117509128349268206338753159905402713941305566545949153372813786136878957799312849759264512666655886972292626420517776751196800533428209013549867420167512762465032428797741651910495918780139165774827106976189033678213377431597261739909035349222595786003325088655562024452479396015877867926856753407856420299633986139248543269788372517030334054320429616020049507954995207387282112189475663800269848272510064316056957200083122782165073089422742353642038382047659278911051840336483756168988787279774818970949450202590421287907349041609736329880033292153618997054830489344419026159418579513037088420917606716031114049645819945733953405577547524848385531949578797570638899032077613673538172067036264892443023275058635373465097050216049378766344910251885570577293922615939831692365769752866267359760125318238378733368482766970539906194634411729283413545390607320744808868208635959249052255232188266171188295382677853688854594388481

@[expose] noncomputable def GC : Nat := nat_lit 270003193259451765699756145823894423284673609464281185594588177935263504046166977245411068490098163265705657685111197058696

@[expose] noncomputable def RH : Nat := nat_lit 10567680155143595575500942614248233439721485073114874215700271532137652678956113370116553975681420239562224670140543954120883532602330887214809358014745821763545740227553665605015809016892614940350195719641168281114796949981679629091201580

@[expose] noncomputable def RHI : Nat := nat_lit 17722230011281942100992728678513860123913994982897231087488723285082885379398177352709212778051054438912897587582602594849202680309697937022890064592528185895487248343467275442945026783042848293196185832982264176711004956038938945622413210

@[expose] noncomputable def S0J : Nat := nat_lit 18479848809548320206391370591064337551618645707672947616055297

@[expose] noncomputable def DPK : Nat :=
  nat_lit 5811584885211485860286980066504689651916784775454965866673431839233

theorem kGens : gensK GC RH RHI = true := by quickRfl
theorem kS0 : s0K PP GC S0J = true := by quickRfl
theorem kTG : wordsK DPK (fun k => tGenWords.getD k []) 13 GC = true := by quickRfl
theorem kRW : wordsK DPK (fun k => rhoWords.getD k []) 25 RH = true := by quickRfl
theorem kC0 : rangeK (closedAt PP MT GC) 0 512 = true := by quickRfl
theorem kC1 : rangeK (closedAt PP MT GC) 512 512 = true := by quickRfl
theorem kC2 : rangeK (closedAt PP MT GC) 1024 512 = true := by quickRfl
theorem kC3 : rangeK (closedAt PP MT GC) 1536 512 = true := by quickRfl
theorem kC4 : rangeK (closedAt PP MT GC) 2048 512 = true := by quickRfl
theorem kC5 : rangeK (closedAt PP MT GC) 2560 512 = true := by quickRfl
theorem kC6 : rangeK (closedAt PP MT GC) 3072 512 = true := by quickRfl
theorem kC7 : rangeK (closedAt PP MT GC) 3584 512 = true := by quickRfl
theorem kC8 : rangeK (closedAt PP MT GC) 4096 512 = true := by quickRfl
theorem kC9 : rangeK (closedAt PP MT GC) 4608 512 = true := by quickRfl
theorem kC10 : rangeK (closedAt PP MT GC) 5120 512 = true := by quickRfl
theorem kC11 : rangeK (closedAt PP MT GC) 5632 512 = true := by quickRfl
theorem kC12 : rangeK (closedAt PP MT GC) 6144 512 = true := by quickRfl
theorem kC13 : rangeK (closedAt PP MT GC) 6656 512 = true := by quickRfl
theorem kC14 : rangeK (closedAt PP MT GC) 7168 512 = true := by quickRfl
theorem kC15 : rangeK (closedAt PP MT GC) 7680 512 = true := by quickRfl
theorem kT0 : rangeK (treeAt PP MT GC) 0 512 = true := by quickRfl
theorem kT1 : rangeK (treeAt PP MT GC) 512 512 = true := by quickRfl
theorem kT2 : rangeK (treeAt PP MT GC) 1024 512 = true := by quickRfl
theorem kT3 : rangeK (treeAt PP MT GC) 1536 512 = true := by quickRfl
theorem kT4 : rangeK (treeAt PP MT GC) 2048 512 = true := by quickRfl
theorem kT5 : rangeK (treeAt PP MT GC) 2560 512 = true := by quickRfl
theorem kT6 : rangeK (treeAt PP MT GC) 3072 512 = true := by quickRfl
theorem kT7 : rangeK (treeAt PP MT GC) 3584 512 = true := by quickRfl
theorem kT8 : rangeK (treeAt PP MT GC) 4096 512 = true := by quickRfl
theorem kT9 : rangeK (treeAt PP MT GC) 4608 512 = true := by quickRfl
theorem kT10 : rangeK (treeAt PP MT GC) 5120 512 = true := by quickRfl
theorem kT11 : rangeK (treeAt PP MT GC) 5632 512 = true := by quickRfl
theorem kT12 : rangeK (treeAt PP MT GC) 6144 512 = true := by quickRfl
theorem kT13 : rangeK (treeAt PP MT GC) 6656 512 = true := by quickRfl
theorem kT14 : rangeK (treeAt PP MT GC) 7168 512 = true := by quickRfl
theorem kT15 : rangeK (treeAt PP MT GC) 7680 512 = true := by quickRfl
theorem kF0 : rangeK (factsAt PP GC RH RHI) 0 512 = true := by quickRfl
theorem kF1 : rangeK (factsAt PP GC RH RHI) 512 512 = true := by quickRfl
theorem kF2 : rangeK (factsAt PP GC RH RHI) 1024 512 = true := by quickRfl
theorem kF3 : rangeK (factsAt PP GC RH RHI) 1536 512 = true := by quickRfl
theorem kF4 : rangeK (factsAt PP GC RH RHI) 2048 512 = true := by quickRfl
theorem kF5 : rangeK (factsAt PP GC RH RHI) 2560 512 = true := by quickRfl
theorem kF6 : rangeK (factsAt PP GC RH RHI) 3072 512 = true := by quickRfl
theorem kF7 : rangeK (factsAt PP GC RH RHI) 3584 512 = true := by quickRfl
theorem kF8 : rangeK (factsAt PP GC RH RHI) 4096 512 = true := by quickRfl
theorem kF9 : rangeK (factsAt PP GC RH RHI) 4608 512 = true := by quickRfl
theorem kF10 : rangeK (factsAt PP GC RH RHI) 5120 512 = true := by quickRfl
theorem kF11 : rangeK (factsAt PP GC RH RHI) 5632 512 = true := by quickRfl
theorem kF12 : rangeK (factsAt PP GC RH RHI) 6144 512 = true := by quickRfl
theorem kF13 : rangeK (factsAt PP GC RH RHI) 6656 512 = true := by quickRfl
theorem kF14 : rangeK (factsAt PP GC RH RHI) 7168 512 = true := by quickRfl
theorem kF15 : rangeK (factsAt PP GC RH RHI) 7680 512 = true := by quickRfl

theorem kC : ∀ q < 16, rangeK (closedAt PP MT GC) (512 * q) 512 = true := by
  intro q hq
  interval_cases q
  exacts [kC0, kC1, kC2, kC3, kC4, kC5, kC6, kC7, kC8, kC9, kC10, kC11, kC12, kC13, kC14, kC15]

theorem kT : ∀ q < 16, rangeK (treeAt PP MT GC) (512 * q) 512 = true := by
  intro q hq
  interval_cases q
  exacts [kT0, kT1, kT2, kT3, kT4, kT5, kT6, kT7, kT8, kT9, kT10, kT11, kT12, kT13, kT14, kT15]

theorem kF : ∀ q < 16, rangeK (factsAt PP GC RH RHI) (512 * q) 512 = true := by
  intro q hq
  interval_cases q
  exacts [kF0, kF1, kF2, kF3, kF4, kF5, kF6, kF7, kF8, kF9, kF10, kF11, kF12, kF13, kF14, kF15]

end CertificateChecks.KernelLC.W3186

end

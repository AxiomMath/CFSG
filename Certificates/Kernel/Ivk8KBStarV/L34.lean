module

public import Certificates.Data.Kernel.Ivk8KBStarV
public import Certificates.Kernel.Ivk8KBNorm.L34

public section

namespace CFSG.KS.Ivk8KBStarV.L34

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm CFSG.KS.Ivk8KBStarV

@[expose] noncomputable def r2 : VP 42 :=
  mkV 42 (4137170163328170716152306553158252349675136456161002234232822694495453716544,
    4137170163328170716152306553158252349675136456161002234232822694495453716544)
    (by decide +kernel)

@[expose] noncomputable def r3 : VP 42 :=
  mkV 42 (2295638705432430871099078327757906210488606375433558245511675722962655344021,
    2295638705432430871099078327757906210488606375433558245511675722962655344021)
    (by decide +kernel)

@[expose] def wy03 : List ℤ := [1, 4, -1]

@[expose] noncomputable def y03 : VP 42 :=
  mkV 42 (4248481480268125572204418158446135936292785791249555178311921931070999117888,
    3788989144823370059584286834319351934809374597288558540784407300758855233600)
    (by decide +kernel)

@[expose] noncomputable def y3 : VP 42 :=
  mkV 42 (4029333375731133465266316549235792858047137147608942922134369139076081147909,
    3690182853710350697577379650375525569555919254572882045203638987322687787329)
    (by decide +kernel)

@[expose] def wy17 : List ℤ := [1, 2]

@[expose] noncomputable def y17 : VP 42 :=
  mkV 42 (4253694901240463789717384990430224226431719962662411440352330625515546255493,
    3230914796778322862613400720302108903488497860062621296105857908920889381193)
    (by decide +kernel)

@[expose] def wy25 : List ℤ := [1, 2, 6, 3, 6, 2]

@[expose] noncomputable def y25 : VP 42 :=
  mkV 42 (4350925785865431029346074690447185693562661149270798831622218748529396744389,
    3666915678316927813260853723297058371966645487606890970573805871809670976589)
    (by decide +kernel)

@[expose] def w03 : List (List ℤ) := [[1, 2, -1, 2, 1, 2, 1, 2, -1, 2]]

@[expose] def w13 : List (List ℤ) := [[-1, 2, 1, 2]]

@[expose] def w17 : List (List ℤ) := [[2], [1, 2, -1, 2, 1, 2, -1]]

@[expose] def w23 : List (List ℤ) := [[2, 3, 1, 3, -1, 2, -1, 3, 1, 2, 3]]

@[expose] def w25 : List (List ℤ) :=
  [[1], [2, 1, 2, 1, 2, -1, 2, 1, 2, 1, 2], [1, 3, -1, 2, 3, -1, 3, -1, 2, 3, 1, 2]]

@[expose] noncomputable def W03 : List (VP 42) :=
  [mkV 42 (3322791598920123373160768160795418301665617405122455118543973438586402902144,
    3236022911345217752606645342744091386967759905161471580976937300284681490560)
    (by decide +kernel)]

@[expose] noncomputable def W13 : List (VP 42) :=
  [mkV 42 (3691648605323017040653814798065860477398915874042344166590180224028235567744,
    4575044477229826669517859874558541989644365170774283564756069466534042182208)
    (by decide +kernel)]

@[expose] noncomputable def W17 : List (VP 42) :=
  [mkV 42 (4248481535043882067047787218270844552694957965727465989626547830875589747264,
    4248481535043882067047787218270844552694957965727465989626547830875589747264)
    (by decide +kernel),
  mkV 42 (4137142987700308802217430501917742239032222596056613318329467320438079103558,
    4137142987700308802217430501917742239032222596056613318329467320438079103558)
    (by decide +kernel)]

@[expose] noncomputable def W23 : List (VP 42) :=
  [mkV 42 (2440970121329784960650048171450345364810749888007610077748807200337106342094,
    2875558537774710180449314908143362156448608873849483423465981708180134363924)
    (by decide +kernel)]

@[expose] noncomputable def W25 : List (VP 42) :=
  [mkV 42 (4029333375731133465266316549235792858047137147608942922134369139076081147909,
    3690182853710350697577379650375525569555919254572882045203638987322687787329)
    (by decide +kernel),
  mkV 42 (4024119557960408102548988889990745754965794399507704316003466989245239681344,
    4024119557960408102548988889990745754965794399507704316003466989245239681344)
    (by decide +kernel),
  mkV 42 (4137164486651738066757616903339846389997855395491780658934876285323313947789,
    2993661221606083014930687212550238758552558115852796985607888083207473341329)
    (by decide +kernel)]

@[expose] def qGens : List (List ℤ) := [[1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2], [1]]

@[expose] noncomputable def qStrong : List (VP 42) :=
  [mkV 42 (3674199292741541045514619572937567628722874712317446847342438921280659406912,
    4024119496653641590159159420294916367688633361214211514974017820186586918976)
    (by decide +kernel),
  mkV 42 (4029333375731133465266316549235792858047137147608942922134369139076081147909,
    3690182853710350697577379650375525569555919254572882045203638987322687787329)
    (by decide +kernel)]

set_option maxRecDepth 100000

theorem ch5251_r2 : ((evV Ivk8Norm.L34.gens [5]).1 == r2.1) = true := by quickRfl

theorem ch5251_r3 : ((evV Ivk8Norm.L34.gens [6]).1 == r3.1) = true := by quickRfl

theorem ch5251_y03 :
    ([y03].map Subtype.val == [wy03].map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by
  quickRfl

theorem ch5251_y3 :
    ([y3].map Subtype.val == [[1]].map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by
  quickRfl

theorem ch5251_y17 :
    ([y17].map Subtype.val == [wy17].map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by
  quickRfl

theorem ch5251_y25 :
    ([y25].map Subtype.val == [wy25].map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by
  quickRfl

theorem ch5251_W03 :
    (W03.map Subtype.val == w03.map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by quickRfl

theorem ch5251_W13 :
    (W13.map Subtype.val == w13.map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by quickRfl

theorem ch5251_W17 :
    (W17.map Subtype.val == w17.map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by quickRfl

theorem ch5251_W23 :
    (W23.map Subtype.val == w23.map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by quickRfl

theorem ch5251_W25 :
    (W25.map Subtype.val == w25.map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by quickRfl

theorem ch5251_qGens :
    (qStrong.map Subtype.val == qGens.map fun w => (evV Ivk8Norm.L34.gens w).1) = true := by
  quickRfl

theorem ch5251_c03 : commOK Ivk8Norm.L34.r (y03 :: W03) = true := by quickRfl

theorem ch5251_c13 : commOK r2 (y3 :: W13) = true := by quickRfl

theorem ch5251_c17 : commOK r2 (y17 :: W17) = true := by quickRfl

theorem ch5251_c23 : commOK r3 (y3 :: W23) = true := by quickRfl

theorem ch5251_c25 : commOK r3 (y25 :: W25) = true := by quickRfl

theorem ch5251_cq : commOK Ivk8KBNorm.L34.r4 qStrong = true := by quickRfl

theorem ch5251_s03 : schV [y03] #v[2] = true := by quickRfl

theorem ch5251_o03 : (ordV [y03] #v[2] == 3) = true := by quickRfl

theorem ch5251_s3 : schV [y3] #v[0] = true := by quickRfl

theorem ch5251_o3 : (ordV [y3] #v[0] == 3) = true := by quickRfl

theorem ch5251_s17 : schV [y17] #v[0] = true := by quickRfl

theorem ch5251_o17 : (ordV [y17] #v[0] == 7) = true := by quickRfl

theorem ch5251_s25 : schV [y25] #v[0] = true := by quickRfl

theorem ch5251_o25 : (ordV [y25] #v[0] == 5) = true := by quickRfl

theorem ch5251_sq : schV qStrong #v[0, 2] = true := by quickRfl

theorem ch5251_oq : (ordV qStrong #v[0, 2] == 9) = true := by quickRfl

theorem ch5251_row03 : rowOK 3 W03 (enumV [y03] #v[2]) = true := by quickRfl

theorem ch5251_row13 : rowOK 3 W13 (enumV [y3] #v[0]) = true := by quickRfl

theorem ch5251_row17 : rowOK 7 W17 (enumV [y17] #v[0]) = true := by quickRfl

theorem ch5251_row23 : rowOK 3 W23 (enumV [y3] #v[0]) = true := by quickRfl

theorem ch5251_row25 : rowOK 5 W25 (enumV [y25] #v[0]) = true := by quickRfl

theorem ch5251_moves : movesOK Ivk8KBNorm.L34.d4 (enumV qStrong #v[0, 2]) = true := by quickRfl

end CFSG.KS.Ivk8KBStarV.L34

end

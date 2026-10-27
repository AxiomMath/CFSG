module

public import Certificates.Kernel.YoshQ.RecA
public import Certificates.Kernel.YoshQ.RecN
public import Certificates.Kernel.YoshQ.RecW
public import Certificates.Kernel.YoshQ.Gens
public import CFSG.Certificates.Kernel.YoshQ.ParamSound
public import CFSG.Certificates.Kernel.YoshQ.TwinSound

public section

namespace CertificateChecks.KernelYoshQ

open CFSG.KC.YoshQ CFSG.EvenSporadicStandard.M12Std.Yosh CFSG.EvenSporadicStandard.Fin76b

theorem y_ok : RecOK 14 5 14 2000 yGens Y.GS Y.RL Y.cnt Y.EP Y.PL Y.POS Y.SM Y.SF :=
  ⟨(gensOK_spec g_y).1, y_rec.1, y_rec.2⟩
theorem k_ok : RecOK 14 5 14 4000 kTabs K.GS K.RL K.cnt K.EP K.PL K.POS K.SM K.SF :=
  ⟨(gensOK_spec g_k).1, k_rec.1, k_rec.2⟩
theorem r_ok : RecOK 14 5 14 4000 rTabs R.GS R.RL R.cnt R.EP R.PL R.POS R.SM R.SF :=
  ⟨(gensOK_spec g_r).1, r_rec.1, r_rec.2⟩
theorem eg_ok : RecOK 16 5 16 4000 eGens EG.GS EG.RL EG.cnt EG.EP EG.PL EG.POS EG.SM EG.SF :=
  ⟨(gensOK_spec g_eg.1).1, eg_rec.1, eg_rec.2⟩
theorem q00_ok : RecOK 24 5 24 4000 (qGens 0 0) Q00.GS Q00.RL Q00.cnt Q00.EP Q00.PL Q00.POS Q00.SM
    Q00.SF := ⟨(gensOK_spec g_q00.1).1, q00_rec.1, q00_rec.2⟩
theorem q01_ok : RecOK 24 5 24 4000 (qGens 0 1) Q01.GS Q01.RL Q01.cnt Q01.EP Q01.PL Q01.POS Q01.SM
    Q01.SF := ⟨(gensOK_spec g_q01.1).1, q01_rec.1, q01_rec.2⟩
theorem q10_ok : RecOK 24 5 24 4000 (qGens 1 0) Q10.GS Q10.RL Q10.cnt Q10.EP Q10.PL Q10.POS Q10.SM
    Q10.SF := ⟨(gensOK_spec g_q10.1).1, q10_rec.1, q10_rec.2⟩
theorem q11_ok : RecOK 24 5 24 4000 (qGens 1 1) Q11.GS Q11.RL Q11.cnt Q11.EP Q11.PL Q11.POS Q11.SM
    Q11.SF := ⟨(gensOK_spec g_q11.1).1, q11_rec.1, q11_rec.2⟩
theorem n00_ok : RecOK 16 5 16 4000 (nGens 0 0) N00.GS N00.RL N00.cnt N00.EP N00.PL N00.POS N00.SM
    N00.SF := ⟨(gensOK_spec g_n00.1).1, n00_rec.1, n00_rec.2.1⟩
theorem n01_ok : RecOK 16 5 16 4000 (nGens 0 1) N01.GS N01.RL N01.cnt N01.EP N01.PL N01.POS N01.SM
    N01.SF := ⟨(gensOK_spec g_n01.1).1, n01_rec.1, n01_rec.2.1⟩
theorem n10_ok : RecOK 16 5 16 4000 (nGens 1 0) N10.GS N10.RL N10.cnt N10.EP N10.PL N10.POS N10.SM
    N10.SF := ⟨(gensOK_spec g_n10.1).1, n10_rec.1, n10_rec.2.1⟩
theorem n11_ok : RecOK 16 5 16 4000 (nGens 1 1) N11.GS N11.RL N11.cnt N11.EP N11.PL N11.POS N11.SM
    N11.SF := ⟨(gensOK_spec g_n11.1).1, n11_rec.1, n11_rec.2.1⟩
theorem ne00_ok : RecOK 16 5 16 4000 (nEGens 0 0) NE00.GS NE00.RL NE00.cnt NE00.EP NE00.PL NE00.POS
    NE00.SM NE00.SF := ⟨(gensOK_spec g_ne.1).1, ne_rec.1.1, ne_rec.1.2⟩
theorem ne01_ok : RecOK 16 5 16 4000 (nEGens 0 1) NE01.GS NE01.RL NE01.cnt NE01.EP NE01.PL NE01.POS
    NE01.SM NE01.SF := ⟨(gensOK_spec g_ne.2.1).1, ne_rec.2.1.1, ne_rec.2.1.2⟩
theorem ne10_ok : RecOK 16 5 16 4000 (nEGens 1 0) NE10.GS NE10.RL NE10.cnt NE10.EP NE10.PL NE10.POS
    NE10.SM NE10.SF := ⟨(gensOK_spec g_ne.2.2.1).1, ne_rec.2.2.1.1, ne_rec.2.2.1.2⟩
theorem ne11_ok : RecOK 16 5 16 4000 (nEGens 1 1) NE11.GS NE11.RL NE11.cnt NE11.EP NE11.PL NE11.POS
    NE11.SM NE11.SF := ⟨(gensOK_spec g_ne.2.2.2).1, ne_rec.2.2.2.1, ne_rec.2.2.2.2⟩
theorem e00_ok : RecOK 16 5 16 4000 (wgens 0 0 eWords) E00.GS E00.RL E00.cnt E00.EP E00.PL E00.POS
    E00.SM E00.SF := ⟨(gensOK_spec g_e.1).1, e_rec.1.1, e_rec.1.2⟩
theorem e01_ok : RecOK 16 5 16 4000 (wgens 0 1 eWords) E01.GS E01.RL E01.cnt E01.EP E01.PL E01.POS
    E01.SM E01.SF := ⟨(gensOK_spec g_e.2.1).1, e_rec.2.1.1, e_rec.2.1.2⟩
theorem e10_ok : RecOK 16 5 16 4000 (wgens 1 0 eWords) E10.GS E10.RL E10.cnt E10.EP E10.PL E10.POS
    E10.SM E10.SF := ⟨(gensOK_spec g_e.2.2.1).1, e_rec.2.2.1.1, e_rec.2.2.1.2⟩
theorem e11_ok : RecOK 16 5 16 4000 (wgens 1 1 eWords) E11.GS E11.RL E11.cnt E11.EP E11.PL E11.POS
    E11.SM E11.SF := ⟨(gensOK_spec g_e.2.2.2).1, e_rec.2.2.2.1, e_rec.2.2.2.2⟩
theorem s00_ok : RecOK 16 5 16 4000 (wgens 0 0 sWords) S00.GS S00.RL S00.cnt S00.EP S00.PL S00.POS
    S00.SM S00.SF := ⟨(gensOK_spec g_s.1).1, s00_rec.1, s00_rec.2⟩
theorem s01_ok : RecOK 16 5 16 4000 (wgens 0 1 sWords) S01.GS S01.RL S01.cnt S01.EP S01.PL S01.POS
    S01.SM S01.SF := ⟨(gensOK_spec g_s.2.1).1, s01_rec.1, s01_rec.2⟩
theorem s10_ok : RecOK 16 5 16 4000 (wgens 1 0 sWords) S10.GS S10.RL S10.cnt S10.EP S10.PL S10.POS
    S10.SM S10.SF := ⟨(gensOK_spec g_s.2.2.1).1, s10_rec.1, s10_rec.2⟩
theorem s11_ok : RecOK 16 5 16 4000 (wgens 1 1 sWords) S11.GS S11.RL S11.cnt S11.EP S11.PL S11.POS
    S11.SM S11.SF := ⟨(gensOK_spec g_s.2.2.2).1, s11_rec.1, s11_rec.2⟩
theorem a10_ok : RecOK 16 5 16 4000 (wgens 1 0 aWords) A10.GS A10.RL A10.cnt A10.EP A10.PL A10.POS
    A10.SM A10.SF := ⟨(gensOK_spec g_a.1).1, a_rec.1.1, a_rec.1.2⟩
theorem a11_ok : RecOK 16 5 16 4000 (wgens 1 1 aWords) A11.GS A11.RL A11.cnt A11.EP A11.PL A11.POS
    A11.SM A11.SF := ⟨(gensOK_spec g_a.2).1, a_rec.2.1.1, a_rec.2.1.2⟩
theorem ge10_ok : RecOK 16 5 16 4000 ((GE10.GS.map (tabN 16 5)).toArray) GE10.GS GE10.RL GE10.cnt
    GE10.EP GE10.PL GE10.POS GE10.SM GE10.SF := ⟨rfl, a_rec.2.2.1.1, a_rec.2.2.1.2⟩
theorem ge11_ok : RecOK 16 5 16 4000 ((GE11.GS.map (tabN 16 5)).toArray) GE11.GS GE11.RL GE11.cnt
    GE11.EP GE11.PL GE11.POS GE11.SM GE11.SF := ⟨rfl, a_rec.2.2.2.1, a_rec.2.2.2.2⟩
theorem gl0_ok : RecOK 28 5 16 4000 (glueGens (wgens 1 0 sWords) (sylowHomData 0)) GL0.GS GL0.RL
    GL0.cnt GL0.EP GL0.PL GL0.POS GL0.SM GL0.SF := ⟨(gensOK_spec g_gl.1).1, gl0_rec.1, gl0_rec.2⟩
theorem gl1_ok : RecOK 28 5 16 4000 (glueGens (wgens 1 1 sWords) (sylowHomData 1)) GL1.GS GL1.RL
    GL1.cnt GL1.EP GL1.PL GL1.POS GL1.SM GL1.SF := ⟨(gensOK_spec g_gl.2).1, gl1_rec.1, gl1_rec.2⟩

theorem nData_of {α k : Nat} {GS RL : List Nat} {cnt EP PL POS : Nat} {SM SF : List Nat}
    (R : RecOK 16 5 16 4000 (nGens α k) GS RL cnt EP PL POS SM SF) (hl : GS.length = 9) :
    NData α k GS RL :=
  ⟨R.gens_eq, hl, R.closure_fst (by decide) (by decide) (by decide) (Nat.le_refl _)⟩

theorem n00_data : NData 0 0 N00.GS N00.RL := nData_of n00_ok (by decide)
theorem n01_data : NData 0 1 N01.GS N01.RL := nData_of n01_ok (by decide)
theorem n10_data : NData 1 0 N10.GS N10.RL := nData_of n10_ok (by decide)
theorem n11_data : NData 1 1 N11.GS N11.RL := nData_of n11_ok (by decide)

end CertificateChecks.KernelYoshQ

end

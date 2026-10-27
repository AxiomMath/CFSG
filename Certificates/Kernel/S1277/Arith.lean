module

public import Certificates.Data.Kernel.S1277KArith
public import Certificates.Kernel.S1277.LatData
public import Certificates.Kernel.S1277.CandData
public import Certificates.Kernel.S1277.FrData
public import Certificates.Kernel.S1277.SigData
public import Certificates.Kernel.S1277.ArithData
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Lce

public section

namespace CFSG.KP.S1277Ar

open CFSG.KC.S1277Ar CFSG.KD.S1277Lat CFSG.KD.S1277Cand CFSG.KD.S1277Fr CFSG.KD.S1277Sig
  CFSG.KD.S1277Ar

theorem x_ok : xChk (sd.getD xi 0) (sl.getD xi 0) xu xt = true := by quickRfl

theorem ar_g : arAll 24 olg xi svg nxg sgig sgdg sglg sxg sd sl sT brg bkg = true := by quickRfl
theorem ar_n : arAll 48 oln xi svn nxn sgin sgdn sgln sxn sd sl sT brn bkn = true := by quickRfl

theorem cov_g : covChk nmg.length ncig vig nfig sgig = true := by quickRfl
theorem cov_n : covChk nmn.length ncin vin nfin sgin = true := by quickRfl

theorem svn_eq : svn = 14 := by decide +kernel

end CFSG.KP.S1277Ar

end

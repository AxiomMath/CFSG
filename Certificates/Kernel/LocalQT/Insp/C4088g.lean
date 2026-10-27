module

public import Certificates.Kernel.LocalQT.Insp.C4088t
public import CFSG.Certificates.Kernel.LocalQTInspSound
public import CFSG.Certificates.Kernel.LocalQTSylESound

public section

namespace CFSG.KD.LQT.C4088

open CFSG.KC.LQT.Insp CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.QuasithinUnique.Vol2Native.L239
  CFSG.QuasithinUnique.Vol2Native.L239.M23Insp CFSG.Blueprint

theorem T_reach : Reach data.ks data.t₀ data.T data.tp data.tl :=
  reach23_sound ks (codes_gens _ (by decide) gens hGg ksWords) tupleCodes tupleParent tupleLabel
    5516578 kR

theorem T_nodup : (data.T.map enc).Nodup := codes23_sound tupleCodes kN

end CFSG.KD.LQT.C4088

end

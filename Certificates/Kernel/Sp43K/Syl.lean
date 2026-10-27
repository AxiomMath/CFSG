module

public import Certificates.Kernel.Sp43K.Sel5
public import CFSG.Certificates.Kernel.Common.EachTrue
public import Certificates.Kernel.Sp43K.Sel4

public section

#kc_each CFSG.KD.Sp43K ch1322001s_ CFSG.KD.Sp43K.sylC 0 8

#kc_each CFSG.KD.Sp43K ch1322001fix (fun _ => CFSG.KD.Sp43K.fixC) 0 1

#kc_each CFSG.KD.Sp43K ch1322001ne (fun _ => CFSG.KD.Sp43K.noEigC) 0 1

end

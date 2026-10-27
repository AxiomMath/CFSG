module

public import Certificates.Kernel.Sp43K.Sel4
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KD.Sp43K ch1322001sp_ CFSG.KD.Sp43K.spC 0 5

#kc_each CFSG.KD.Sp43K ch1322001sp5 (fun _ => CFSG.KD.Sp43K.sp5C) 0 1

#kc_each CFSG.KD.Sp43K ch1322001h3 (fun _ => CFSG.KD.Sp43K.h3C) 0 1

#kc_each CFSG.KD.Sp43K ch1322001h4 (fun _ => CFSG.KD.Sp43K.h4C) 0 1

#kc_each CFSG.KD.Sp43K ch1322001b (fun _ => CFSG.KD.Sp43K.bC) 0 1

#kc_each CFSG.KD.Sp43K ch1322001n0 (fun _ => CFSG.KD.Sp43K.n0C) 0 1

end

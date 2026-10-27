module

public import Certificates.Data.Kernel.LyI301.Defs
import CFSG.Certificates.Kernel.Common.EachTrue

set_option Elab.async false

public section

open CFSG.KC.LyI301

#kc_each CFSG.KC.LyI301 ly810304row (fun r => lyRow r) 0 12

end

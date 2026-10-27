module

public import Certificates.Kernel.LocalComp.L34F946Gen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.LocalComp.L34F946Gen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelLC.L34F946.WA include_bytes "data/L34F946Data.WA.items" 1080 2075152477133985816
#kc_items CertificateChecks.KernelLC.L34F946.WZ include_bytes "data/L34F946Data.WZ.items" 984 2135439290037835843
#kc_items CertificateChecks.KernelLC.L34F946.KS include_bytes "data/L34F946Data.KS.items" 14 9403930371866034271

end
